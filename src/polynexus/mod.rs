use crate::{
    Engine, McProof, McResult, McWitness, MpEngine, MpMcResult,
    config::{EngineConfigBase, PreprocConfig},
    ic3::{IC3, IC3Config},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    transys::{Transys, certify::Restore},
};
use clap::Args;
use log::{LevelFilter, set_max_level};
use logicrs::VarSymbols;
use serde::{Deserialize, Serialize};
use std::{
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread::{self, JoinHandle},
    time::Duration,
};

#[derive(Args, Clone, Debug, Serialize, Deserialize, Default)]
pub struct PolyNexusConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,

    /// Number of worker threads (0 = auto-detect)
    #[arg(long = "workers", default_value_t = 0)]
    pub workers: usize,
}

impl_config_deref!(PolyNexusConfig);

fn ic3_presets() -> Vec<IC3Config> {
    let mut presets = Vec::new();
    let base = || {
        let mut c = IC3Config::default();
        c.pred_prop = true;
        c
    };
    presets.push(base());
    {
        let mut c = base();
        c.inn = true;
        presets.push(c);
    }
    {
        let mut c = base();
        c.abs_cst = true;
        c.ctp = true;
        presets.push(c);
    }
    {
        let mut c = base();
        c.dynamic = true;
        c.drop_po = false;
        presets.push(c);
    }
    {
        let mut c = base();
        c.inn = true;
        c.base.rseed = 42;
        presets.push(c);
    }
    {
        let mut c = base();
        c.ctp = true;
        c.base.rseed = 123;
        presets.push(c);
    }
    presets
}

struct PropTracerBridge {
    prop: usize,
    tx: mpsc::Sender<WorkerMsg>,
}

impl TracerIf for PropTracerBridge {
    fn trace_res(&mut self, _prop: Option<usize>, res: McResult) {
        let _ = self.tx.send(WorkerMsg::Progress {
            prop: self.prop,
            result: res,
        });
    }
}

enum WorkerMsg {
    Started {
        #[allow(unused)]
        prop: usize,
        stop_ctrl: Arc<AtomicBool>,
    },
    Progress {
        prop: usize,
        result: McResult,
    },
    Done {
        prop: usize,
        result: McResult,
        ic3: Box<IC3>,
    },
}

unsafe impl Send for WorkerMsg {}

struct Scheduler {
    num_props: usize,
    resolved: Vec<bool>,
    num_resolved: usize,
    active_workers: Vec<usize>,
    preset_counter: Vec<usize>,
    prop_stops: Vec<Arc<AtomicBool>>,
    presets: Vec<IC3Config>,
}

impl Scheduler {
    fn new(num_props: usize, presets: Vec<IC3Config>) -> Self {
        Self {
            num_props,
            resolved: vec![false; num_props],
            num_resolved: 0,
            active_workers: vec![0; num_props],
            preset_counter: vec![0; num_props],
            prop_stops: (0..num_props)
                .map(|_| Arc::new(AtomicBool::new(false)))
                .collect(),
            presets,
        }
    }

    /// Pick the unresolved property with fewest active workers, return (prop, cfg).
    fn next(&mut self) -> Option<(usize, IC3Config)> {
        let mut best = None;
        let mut min_active = usize::MAX;
        for p in 0..self.num_props {
            if !self.resolved[p] && self.active_workers[p] < min_active {
                min_active = self.active_workers[p];
                best = Some(p);
            }
        }
        let prop = best?;
        let idx = self.preset_counter[prop];
        self.preset_counter[prop] += 1;
        let preset_idx = idx % self.presets.len();
        let mut cfg = self.presets[preset_idx].clone();
        cfg.prop = Some(prop);
        cfg.base.rseed = cfg.base.rseed.wrapping_add(idx as u64);
        self.active_workers[prop] += 1;
        Some((prop, cfg))
    }

    fn worker_done(&mut self, prop: usize) {
        self.active_workers[prop] = self.active_workers[prop].saturating_sub(1);
    }

    fn resolve(&mut self, prop: usize) {
        if !self.resolved[prop] {
            self.resolved[prop] = true;
            self.num_resolved += 1;
            self.prop_stops[prop].store(true, Ordering::Relaxed);
        }
    }

    fn all_resolved(&self) -> bool {
        self.num_resolved == self.num_props
    }

    fn prop_stop(&self, prop: usize) -> Arc<AtomicBool> {
        self.prop_stops[prop].clone()
    }
}

pub struct PolyNexus {
    #[allow(unused)]
    cfg: PolyNexusConfig,
    ts: Transys,
    #[allow(unused)]
    rst: Restore,
    tracer: Tracer,
    stop_ctrl: Arc<AtomicBool>,
    results: MpMcResult,
    ic3s: Vec<Option<Box<IC3>>>,
}

impl PolyNexus {
    pub fn new(cfg: PolyNexusConfig, ts: Transys, res: MpMcResult) -> Self {
        let rst = Restore::new(&ts);
        let (ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        let mut ts = ts;
        ts.remove_gate_init(&mut rst);
        let num_props = ts.bad.len();
        Self {
            cfg,
            ts,
            rst,
            tracer: Tracer::new(),
            stop_ctrl: Arc::new(AtomicBool::new(false)),
            results: res,
            ic3s: (0..num_props).map(|_| None).collect(),
        }
    }

    fn num_workers(&self) -> usize {
        if self.cfg.workers > 0 {
            self.cfg.workers
        } else {
            thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        }
    }

    fn run(&mut self) -> MpMcResult {
        let num_props = self.ts.bad.len();
        let num_workers = self.num_workers();
        let presets = ic3_presets();
        let scheduler = Arc::new(Mutex::new(Scheduler::new(num_props, presets)));
        let (tx, rx) = mpsc::channel();
        let mut joins: Vec<JoinHandle<()>> = Vec::new();

        for _ in 0..num_workers {
            let sched = scheduler.clone();
            let ts = self.ts.clone();
            let tx = tx.clone();
            let join = thread::spawn(move || {
                set_max_level(LevelFilter::Warn);
                loop {
                    let (prop, cfg, p_stop) = {
                        let mut s = sched.lock().unwrap();
                        match s.next() {
                            Some((prop, cfg)) => (prop, cfg, s.prop_stop(prop)),
                            None => break,
                        }
                    };
                    if p_stop.load(Ordering::Relaxed) {
                        sched.lock().unwrap().worker_done(prop);
                        continue;
                    }
                    let mut ic3 = IC3::new(cfg, ts.clone(), VarSymbols::default());
                    let ic3_stop = ic3.get_stop_ctrl();
                    let _ = tx.send(WorkerMsg::Started {
                        prop,
                        stop_ctrl: ic3_stop,
                    });
                    let bridge = PropTracerBridge {
                        prop,
                        tx: tx.clone(),
                    };
                    ic3.add_tracer(Box::new(bridge));
                    let result = ic3.check();
                    let _ = tx.send(WorkerMsg::Done {
                        prop,
                        result,
                        ic3: Box::new(ic3),
                    });
                    sched.lock().unwrap().worker_done(prop);
                }
            });
            joins.push(join);
        }
        drop(tx);
        self.collect_results(rx, joins, scheduler)
    }

    fn collect_results(
        &mut self,
        rx: mpsc::Receiver<WorkerMsg>,
        joins: Vec<JoinHandle<()>>,
        scheduler: Arc<Mutex<Scheduler>>,
    ) -> MpMcResult {
        let mut engine_stops: Vec<Arc<AtomicBool>> = Vec::new();
        loop {
            if self.stop_ctrl.load(Ordering::Relaxed) {
                for s in &engine_stops {
                    s.store(true, Ordering::Relaxed);
                }
                break;
            }
            match rx.recv_timeout(Duration::from_millis(50)) {
                Ok(WorkerMsg::Started { stop_ctrl, .. }) => {
                    if self.stop_ctrl.load(Ordering::Relaxed) {
                        stop_ctrl.store(true, Ordering::Relaxed);
                    }
                    engine_stops.push(stop_ctrl);
                }
                Ok(WorkerMsg::Progress { prop, result }) => {
                    let sched = scheduler.lock().unwrap();
                    if !sched.resolved[prop] {
                        drop(sched);
                        self.results[prop] = self.results[prop] | result;
                        self.tracer.trace_res(Some(prop), result);
                    }
                }
                Ok(WorkerMsg::Done { prop, result, ic3 }) => {
                    let mut sched = scheduler.lock().unwrap();
                    if !sched.resolved[prop] && !result.is_unknown() {
                        sched.resolve(prop);
                        drop(sched);
                        self.results[prop] = result;
                        self.tracer.trace_res(Some(prop), result);
                        self.ic3s[prop] = Some(ic3);
                    } else {
                        drop(sched);
                        self.results[prop] = self.results[prop] | result;
                        self.tracer.trace_res(Some(prop), result);
                    }
                    if scheduler.lock().unwrap().all_resolved() {
                        break;
                    }
                }
                Err(mpsc::RecvTimeoutError::Timeout) => continue,
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
            }
        }
        self.stop_ctrl.store(true, Ordering::Relaxed);
        for s in &engine_stops {
            s.store(true, Ordering::Relaxed);
        }
        for j in joins {
            let _ = j.join();
        }
        self.results.clone()
    }
}

impl Engine for PolyNexus {
    fn check(&mut self) -> McResult {
        todo!()
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn get_stop_ctrl(&self) -> Arc<AtomicBool> {
        self.stop_ctrl.clone()
    }

    fn proof(&mut self) -> McProof {
        if let Some(ic3) = self.ic3s.iter_mut().flatten().next() {
            return ic3.proof();
        }
        panic!("no proof available");
    }

    fn witness(&mut self) -> McWitness {
        for (i, r) in self.results.iter().enumerate() {
            if r.is_unsafe()
                && let Some(ic3) = self.ic3s[i].as_mut()
            {
                return ic3.witness();
            }
        }
        panic!("no witness available");
    }
}

impl MpEngine for PolyNexus {
    fn check(&mut self) -> MpMcResult {
        self.run()
    }

    fn proof(&mut self, prop: usize) -> McProof {
        self.ic3s[prop]
            .as_mut()
            .expect("no IC3 for this property")
            .proof()
    }

    fn witness(&mut self, prop: usize) -> McWitness {
        self.ic3s[prop]
            .as_mut()
            .expect("no IC3 for this property")
            .witness()
    }
}
