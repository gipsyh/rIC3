mod schd;

use crate::{
    BlCex, BlEngine, BlProof, Engine, McBlCertificate, McResult, MpEngine, MpMcResult,
    config::{EngineConfigBase, PreprocConfig, WorkerConfigs},
    ic3::{IC3, IC3Config},
    impl_config_deref,
    polynexus::schd::Scheduler,
    tracer::{StateTracerIf, Tracer, TracerIf},
    transys::{Transys, certify::Restore},
    utils::{EngineCtrl, StateIpcTx},
};
use clap::Args;
use giputils::{TerminateCtrl, hash::GHashMap};
use ipc_channel::{
    TrySelectError,
    ipc::{self, IpcReceiverSet, IpcSelectionResult, IpcSender},
};
use log::{LevelFilter, info, set_max_level};
use logicrs::VarSymbols;
use nix::{
    errno::Errno,
    sys::{
        signal::{Signal, kill},
        wait::{WaitPidFlag, WaitStatus, waitpid},
    },
    unistd::Pid,
};
use serde::{Deserialize, Serialize};
use std::{
    process::exit,
    sync::Arc,
    thread,
    time::{Duration, Instant},
};

#[derive(Args, Clone, Debug, Serialize, Deserialize, Default)]
pub struct PolyNexusConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,

    /// Number of worker processes (None = auto-detect)
    #[arg(long = "workers")]
    pub workers: Option<usize>,
}

impl_config_deref!(PolyNexusConfig);

type WorkerDoneTx = IpcSender<WorkerDone>;

#[derive(Clone, Debug, Serialize, Deserialize)]
struct WorkerDone {
    prop: usize,
    result: McResult,
    cert: Option<McBlCertificate>,
}

struct RunningWorker {
    prop: usize,
}

pub struct PolyNexus {
    #[allow(unused)]
    cfg: PolyNexusConfig,
    ots: Transys,
    ts: Transys,
    rst: Restore,
    tracer: Tracer,
    ctrl: Arc<EngineCtrl>,
    results: MpMcResult,
    certs: Vec<Option<McBlCertificate>>,
}

impl PolyNexus {
    pub fn new(cfg: PolyNexusConfig, ts: Transys, results: MpMcResult) -> Self {
        let ots = ts.clone();
        let rst = Restore::new(&ts);
        let (ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        let mut ts = ts;
        ts.remove_gate_init(&mut rst);
        let num_props = ts.bad.len();
        Self {
            cfg,
            ots,
            ts,
            rst,
            tracer: Tracer::new(),
            ctrl: Arc::new(EngineCtrl::new()),
            results,
            certs: vec![None; num_props],
        }
    }

    fn num_workers(&self) -> usize {
        self.cfg.workers.unwrap_or_else(|| {
            thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(8)
        })
    }

    fn spawn_worker(
        prop: usize,
        cfg: IC3Config,
        ts: &Transys,
        state_recv: &mut IpcReceiverSet,
        done_recv: &mut IpcReceiverSet,
        running: &mut GHashMap<Pid, RunningWorker>,
        state_ids: &mut GHashMap<u64, Pid>,
        done_ids: &mut GHashMap<u64, Pid>,
    ) {
        let (state_tx, state_rx) = ipc::channel().unwrap();
        let (done_tx, done_rx) = ipc::channel().unwrap();
        match fork::fork().unwrap() {
            fork::Fork::Parent(child) => {
                let pid = Pid::from_raw(child);
                let state_id = state_recv.add(state_rx).unwrap();
                let done_id = done_recv.add(done_rx).unwrap();
                running.insert(pid, RunningWorker { prop });
                state_ids.insert(state_id, pid);
                done_ids.insert(done_id, pid);
                info!("start polynexus worker p{prop}");
            }
            fork::Fork::Child => Self::run_worker(prop, cfg, ts, state_tx, done_tx),
        }
    }

    fn run_worker(
        prop: usize,
        cfg: IC3Config,
        ts: &Transys,
        state_tx: StateIpcTx,
        done_tx: WorkerDoneTx,
    ) -> ! {
        set_max_level(LevelFilter::Warn);
        // We are in the forked child. Take ownership of the inherited model
        // directly, matching the portfolio worker isolation strategy.
        let ts = unsafe { std::ptr::read(ts) };
        let mut ic3 = IC3::new(cfg, ts, VarSymbols::default());
        ic3.add_tracer(Box::new(PropTracerBridge { prop, tx: state_tx }));
        let result = ic3.check();
        let cert = match result {
            McResult::UNSAT => Some(McBlCertificate::UNSAT(ic3.proof())),
            McResult::SAT(_) => Some(McBlCertificate::SAT(ic3.cex())),
            McResult::Unknown(_) => None,
        };
        let _ = done_tx.send(WorkerDone { prop, result, cert });
        exit(0);
    }

    fn terminate_running(running: &mut GHashMap<Pid, RunningWorker>) {
        let pids: Vec<_> = running.keys().copied().collect();
        for pid in &pids {
            let _ = kill(*pid, Signal::SIGTERM);
        }
        for pid in pids {
            loop {
                match waitpid(pid, None) {
                    Ok(WaitStatus::Exited(_, _)) | Ok(WaitStatus::Signaled(_, _, _)) => {
                        running.remove(&pid);
                        break;
                    }
                    Err(Errno::EINTR) => continue,
                    Err(Errno::ECHILD) => {
                        running.remove(&pid);
                        break;
                    }
                    Err(err) => panic!("polynexus waitpid failed: {err}"),
                    _ => panic!(),
                }
            }
        }
    }

    fn reap_finished(running: &mut GHashMap<Pid, RunningWorker>) {
        let pids: Vec<_> = running.keys().copied().collect();
        for pid in pids {
            loop {
                match waitpid(pid, Some(WaitPidFlag::WNOHANG)) {
                    Ok(WaitStatus::StillAlive) => break,
                    Ok(WaitStatus::Exited(_, code)) => {
                        if code != 0 {
                            info!(
                                "polynexus worker p{} exited with code {code}",
                                running[&pid].prop
                            );
                        }
                        running.remove(&pid);
                        break;
                    }
                    Ok(WaitStatus::Signaled(_, sig, _)) => {
                        info!(
                            "polynexus worker p{} terminated by {sig}",
                            running[&pid].prop
                        );
                        running.remove(&pid);
                        break;
                    }
                    Err(Errno::EINTR) => continue,
                    Err(Errno::ECHILD) => {
                        running.remove(&pid);
                        break;
                    }
                    Err(err) => panic!("polynexus waitpid failed: {err}"),
                    _ => panic!(),
                }
            }
        }
    }

    fn fill_workers(
        &mut self,
        num_workers: usize,
        sched: &mut Scheduler,
        state_recv: &mut IpcReceiverSet,
        done_recv: &mut IpcReceiverSet,
        running: &mut GHashMap<Pid, RunningWorker>,
        state_ids: &mut GHashMap<u64, Pid>,
        done_ids: &mut GHashMap<u64, Pid>,
    ) {
        while running.len() < num_workers && !sched.all_resolved() {
            let Some((prop, cfg)) = sched.pick() else {
                break;
            };
            Self::spawn_worker(
                prop, cfg, &self.ts, state_recv, done_recv, running, state_ids, done_ids,
            );
        }
    }

    fn poll_state_traces(
        &mut self,
        sched: &Scheduler,
        unknown_bound: &mut Vec<Option<usize>>,
        state_recv: &mut IpcReceiverSet,
        state_ids: &mut GHashMap<u64, Pid>,
    ) {
        let events = match state_recv.try_select() {
            Ok(events) => events,
            Err(TrySelectError::Empty) => return,
            Err(err) => panic!("polynexus trace select failed: {err}"),
        };
        for event in events {
            match event {
                IpcSelectionResult::MessageReceived(id, message) => {
                    if !state_ids.contains_key(&id) {
                        continue;
                    }
                    let (prop, result): (Option<usize>, McResult) = message.to().unwrap();
                    let Some(prop) = prop else {
                        continue;
                    };
                    if prop < sched.num_props && !sched.resolved[prop] {
                        self.merge_and_trace(prop, result, unknown_bound);
                    }
                }
                IpcSelectionResult::ChannelClosed(id) => {
                    state_ids.remove(&id);
                }
            }
        }
    }

    fn poll_done(
        &mut self,
        sched: &mut Scheduler,
        unknown_bound: &mut Vec<Option<usize>>,
        done_recv: &mut IpcReceiverSet,
        done_ids: &mut GHashMap<u64, Pid>,
    ) {
        let events = match done_recv.try_select_timeout(Duration::from_millis(10)) {
            Ok(events) => events,
            Err(TrySelectError::Empty) => return,
            Err(err) => panic!("polynexus done select failed: {err}"),
        };
        for event in events {
            match event {
                IpcSelectionResult::MessageReceived(id, message) => {
                    if done_ids.remove(&id).is_none() {
                        continue;
                    }
                    let done: WorkerDone = message.to().unwrap();
                    self.on_worker_done(done, sched, unknown_bound);
                }
                IpcSelectionResult::ChannelClosed(id) => {
                    done_ids.remove(&id);
                }
            }
        }
    }

    fn on_worker_done(
        &mut self,
        done: WorkerDone,
        sched: &mut Scheduler,
        unknown_bound: &mut Vec<Option<usize>>,
    ) {
        let WorkerDone { prop, result, cert } = done;
        if sched.resolved[prop] {
            return;
        }
        if !result.is_unknown() {
            sched.resolve(prop);
            self.results[prop] = result;
            self.tracer.trace_state(Some(prop), result);
            let cert = cert.expect("polynexus worker returned a final result without certificate");
            if let McBlCertificate::SAT(cex) = &cert {
                let cex = self.rst.restore_cex(cex);
                self.tracer.trace_cert(&McBlCertificate::SAT(cex));
            }
            self.certs[prop] = Some(cert);
        } else {
            self.merge_and_trace(prop, result, unknown_bound);
        }
    }

    fn run(&mut self) -> MpMcResult {
        let num_workers = self.num_workers();
        let presets = WorkerConfigs::from_toml(include_str!("config.toml"), "bl_default");
        let num_props = self.ts.bad.len();
        let mut sched = Scheduler::new(num_props, presets);
        let mut state_recv = IpcReceiverSet::new().unwrap();
        let mut done_recv = IpcReceiverSet::new().unwrap();
        let mut running = GHashMap::new();
        let mut state_ids = GHashMap::new();
        let mut done_ids = GHashMap::new();
        // Track per-prop unknown bound seen so far — only emit increasing values.
        let mut unknown_bound: Vec<Option<usize>> = vec![None; num_props];
        let start = Instant::now();
        self.fill_workers(
            num_workers,
            &mut sched,
            &mut state_recv,
            &mut done_recv,
            &mut running,
            &mut state_ids,
            &mut done_ids,
        );

        loop {
            if self.ctrl.is_terminated() || self.cfg.time_limit_hit(start) {
                Self::terminate_running(&mut running);
                break;
            }

            self.poll_state_traces(&sched, &mut unknown_bound, &mut state_recv, &mut state_ids);
            self.poll_done(
                &mut sched,
                &mut unknown_bound,
                &mut done_recv,
                &mut done_ids,
            );
            Self::reap_finished(&mut running);
            self.poll_done(
                &mut sched,
                &mut unknown_bound,
                &mut done_recv,
                &mut done_ids,
            );
            if sched.all_resolved() {
                break;
            }
            self.fill_workers(
                num_workers,
                &mut sched,
                &mut state_recv,
                &mut done_recv,
                &mut running,
                &mut state_ids,
                &mut done_ids,
            );
        }

        if !running.is_empty() {
            Self::terminate_running(&mut running);
        }
        self.results.clone()
    }

    /// Merge `result` into `self.results[prop]`; only call tracer when the
    /// Unknown bound strictly increases (or transitions to Safe/Unsafe).
    fn merge_and_trace(
        &mut self,
        prop: usize,
        result: McResult,
        unknown_bound: &mut Vec<Option<usize>>,
    ) {
        let merged = self.results[prop] | result;
        if merged == self.results[prop] {
            return;
        }
        // For Unknown results, only emit when the depth bound increases.
        if let McResult::Unknown(Some(d)) = merged {
            match unknown_bound[prop] {
                Some(prev) if d <= prev => return,
                _ => unknown_bound[prop] = Some(d),
            }
        }
        self.results[prop] = merged;
        self.tracer.trace_state(Some(prop), merged);
    }
}

// ---------------------------------------------------------------------------
// PropTracerBridge — forwards IC3 per-frame progress to the main thread.
// ---------------------------------------------------------------------------

struct PropTracerBridge {
    prop: usize,
    tx: StateIpcTx,
}

impl TracerIf for PropTracerBridge {}

#[intertrait::cast_to]
impl StateTracerIf for PropTracerBridge {
    fn trace_state(&mut self, _prop: Option<usize>, res: McResult) {
        let _ = self.tx.send((Some(self.prop), res));
    }
}

impl Engine for PolyNexus {
    fn check(&mut self) -> McResult {
        panic!();
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn get_ctrl(&self) -> Arc<dyn TerminateCtrl> {
        self.ctrl.clone()
    }
}

impl MpEngine for PolyNexus {
    fn check(&mut self) -> MpMcResult {
        self.run()
    }

    fn proof(&mut self, prop: usize) -> BlProof {
        let Some(McBlCertificate::UNSAT(proof)) = self.certs[prop].as_ref() else {
            panic!("no proof available for this property");
        };
        self.rst.restore_proof(proof.clone(), &self.ots)
    }

    fn cex(&mut self, prop: usize) -> BlCex {
        let Some(McBlCertificate::SAT(cex)) = self.certs[prop].as_ref() else {
            panic!("no cex available for this property");
        };
        self.rst.restore_cex(cex)
    }
}
