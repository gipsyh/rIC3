use crate::{
    BlCex, BlEngine, BlProof, Engine, EngineCtrl, McBlCertificate, McResult, MpEngine, MpMcResult,
    config::{EngineConfigBase, PreprocConfig},
    ic3::{IC3, IC3Config},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    transys::{Transys, certify::Restore},
};
use clap::Args;
use log::{LevelFilter, set_max_level};
use logicrs::VarSymbols;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::{
    sync::mpsc,
    thread::{self, JoinHandle},
};

#[derive(Args, Clone, Debug, Serialize, Deserialize, Default)]
pub struct PolyNexusConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,

    /// Number of worker threads (None = auto-detect)
    #[arg(long = "workers")]
    pub workers: Option<usize>,
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

enum WorkerMsg {
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

/// Scheduler runs on the main thread — no locks needed.
struct Scheduler {
    num_props: usize,
    resolved: Vec<bool>,
    preset_counter: Vec<usize>,
    presets: Vec<IC3Config>,
}

impl Scheduler {
    fn new(num_props: usize, presets: Vec<IC3Config>) -> Self {
        Self {
            num_props,
            resolved: vec![false; num_props],
            preset_counter: vec![0; num_props],
            presets,
        }
    }

    /// Pick the unresolved property with smallest preset_counter, return (prop, cfg).
    fn next(&mut self) -> Option<(usize, IC3Config)> {
        let mut best = None;
        let mut min_preset = usize::MAX;
        for p in 0..self.num_props {
            if !self.resolved[p] && self.preset_counter[p] < min_preset {
                min_preset = self.preset_counter[p];
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
        Some((prop, cfg))
    }

    fn resolve(&mut self, prop: usize) {
        if !self.resolved[prop] {
            self.resolved[prop] = true;
        }
    }

    fn all_resolved(&self) -> bool {
        self.resolved.iter().all(|x| *x)
    }
}

pub struct PolyNexus {
    #[allow(unused)]
    cfg: PolyNexusConfig,
    ots: Transys,
    ts: Transys,
    rst: Restore,
    tracer: Tracer,
    ctrl: EngineCtrl,
    results: MpMcResult,
    ic3s: Vec<Option<Box<IC3>>>,
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
            ctrl: crate::EngineCtrl::new(),
            results,
            ic3s: (0..num_props).map(|_| None).collect(),
        }
    }

    fn overall_result(results: &MpMcResult) -> McResult {
        let mut unsafe_depth = None;
        let mut unknown_bound = None;
        let mut all_safe = true;
        for result in results.iter() {
            match result {
                McResult::UNSAT => {}
                McResult::SAT(depth) => {
                    unsafe_depth = Some(unsafe_depth.map_or(*depth, |d: usize| d.max(*depth)));
                    all_safe = false;
                }
                McResult::Unknown(bound) => {
                    if let Some(bound) = bound {
                        unknown_bound =
                            Some(unknown_bound.map_or(*bound, |d: usize| d.max(*bound)));
                    }
                    all_safe = false;
                }
            }
        }
        if let Some(depth) = unsafe_depth {
            McResult::SAT(depth)
        } else if all_safe {
            McResult::UNSAT
        } else {
            McResult::Unknown(unknown_bound)
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
        ts: Transys,
        tx: mpsc::Sender<WorkerMsg>,
    ) -> (JoinHandle<()>, EngineCtrl) {
        // Create IC3 on the main thread so we can grab its ctrl.
        let mut ic3 = IC3::new(cfg, ts, VarSymbols::default());
        let ctrl = ic3.get_ctrl();
        ic3.add_tracer(Box::new(PropTracerBridge {
            prop,
            tx: tx.clone(),
        }));
        let handle = thread::spawn(move || {
            set_max_level(LevelFilter::Warn);
            let result = ic3.check();
            let _ = tx.send(WorkerMsg::Done {
                prop,
                result,
                ic3: Box::new(ic3),
            });
        });
        (handle, ctrl)
    }

    fn run(&mut self) -> MpMcResult {
        let num_workers = self.num_workers();
        let presets = ic3_presets();
        let num_props = self.ts.bad.len();
        let mut sched = Scheduler::new(num_props, presets);
        let (tx, rx) = mpsc::channel::<WorkerMsg>();
        let mut joins: Vec<JoinHandle<()>> = Vec::new();
        let mut engine_ctrls: Vec<EngineCtrl> = Vec::new();
        // Track per-prop unknown bound seen so far — only emit increasing values.
        let mut unknown_bound: Vec<Option<usize>> = vec![None; num_props];

        // Seed the initial wave of workers (up to num_workers in flight).
        let mut tasks: Vec<(usize, IC3Config)> = Vec::new();
        while tasks.len() < num_workers {
            match sched.next() {
                Some(t) => tasks.push(t),
                None => break,
            }
        }
        let ts_ref = &self.ts;
        let tx_ref = &tx;
        let spawned: Vec<_> = tasks
            .into_par_iter()
            .map(|(prop, cfg)| Self::spawn_worker(prop, cfg, ts_ref.clone(), tx_ref.clone()))
            .collect();
        for (j, ctrl) in spawned {
            joins.push(j);
            engine_ctrls.push(ctrl);
        }

        loop {
            if self.ctrl.is_terminated() {
                for c in &engine_ctrls {
                    c.terminate();
                }
                break;
            }

            let msg = match rx.try_recv() {
                Ok(m) => m,
                Err(std::sync::mpsc::TryRecvError::Empty) => {
                    std::thread::sleep(std::time::Duration::from_millis(10));
                    continue;
                }
                Err(std::sync::mpsc::TryRecvError::Disconnected) => break,
            };

            match msg {
                WorkerMsg::Progress { prop, result } => {
                    if !sched.resolved[prop] {
                        self.merge_and_trace(prop, result, &mut unknown_bound);
                    }
                }

                WorkerMsg::Done {
                    prop,
                    result,
                    mut ic3,
                } => {
                    if !sched.resolved[prop] {
                        if !result.is_unknown() {
                            // Definitive answer — resolve and record.
                            sched.resolve(prop);
                            self.results[prop] = result;
                            self.tracer.trace_state(Some(prop), result);
                            if result.is_sat() {
                                let cex = ic3.cex();
                                let cex = self.rst.restore_cex(&cex);
                                self.tracer.trace_cert(&McBlCertificate::SAT(cex));
                            }
                            self.ic3s[prop] = Some(ic3);
                        } else {
                            // Still unknown — merge bound, then spawn next preset
                            // for that property (keeps workers busy).
                            self.merge_and_trace(prop, result, &mut unknown_bound);
                            if let Some((next_prop, next_cfg)) = sched.next() {
                                let (j, ctrl) = Self::spawn_worker(
                                    next_prop,
                                    next_cfg,
                                    self.ts.clone(),
                                    tx.clone(),
                                );
                                joins.push(j);
                                engine_ctrls.push(ctrl);
                            }
                        }
                    }

                    if sched.all_resolved() {
                        break;
                    }
                }
            }
        }

        for c in &engine_ctrls {
            c.terminate();
        }
        drop(tx); // allow workers to detect disconnection
        for j in joins {
            let _ = j.join();
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
    tx: mpsc::Sender<WorkerMsg>,
}

impl TracerIf for PropTracerBridge {
    fn trace_state(&mut self, _prop: Option<usize>, res: McResult) {
        let _ = self.tx.send(WorkerMsg::Progress {
            prop: self.prop,
            result: res,
        });
    }
}

// ---------------------------------------------------------------------------
// Engine / MpEngine impls
// ---------------------------------------------------------------------------

impl Engine for PolyNexus {
    fn check(&mut self) -> McResult {
        let results = MpEngine::check(self);
        Self::overall_result(&results)
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn get_ctrl(&self) -> EngineCtrl {
        self.ctrl.clone()
    }
}

impl BlEngine for PolyNexus {
    fn proof(&mut self) -> BlProof {
        let mut proof = BlProof {
            proof: self.ts.clone(),
        };
        let mut found = false;
        for (prop, result) in self.results.iter().enumerate() {
            if result.is_unsat() {
                let subp = self.ic3s[prop]
                    .as_mut()
                    .expect("no IC3 for this property")
                    .proof();
                proof.merge(&subp, &self.ts);
                found = true;
            }
        }
        assert!(found, "no proof available");
        self.rst.restore_proof(proof, &self.ots)
    }

    fn cex(&mut self) -> BlCex {
        for (i, r) in self.results.iter().enumerate() {
            if r.is_sat()
                && let Some(ic3) = self.ic3s[i].as_mut()
            {
                let cex = ic3.cex();
                return self.rst.restore_cex(&cex);
            }
        }
        panic!("no cex available");
    }
}

impl MpEngine for PolyNexus {
    fn check(&mut self) -> MpMcResult {
        self.run()
    }

    fn proof(&mut self, prop: usize) -> BlProof {
        let proof = self.ic3s[prop]
            .as_mut()
            .expect("no IC3 for this property")
            .proof();
        self.rst.restore_proof(proof, &self.ots)
    }

    fn cex(&mut self, prop: usize) -> BlCex {
        let cex = self.ic3s[prop]
            .as_mut()
            .expect("no IC3 for this property")
            .cex();
        self.rst.restore_cex(&cex)
    }
}
