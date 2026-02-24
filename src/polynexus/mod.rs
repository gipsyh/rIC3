use crate::{
    Engine, EngineCtrl, McProof, McResult, McWitness, MpEngine, MpMcResult,
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
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread::{self, JoinHandle},
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
    ctrl: EngineCtrl,
    results: MpMcResult,
    ic3s: Vec<Option<Box<IC3>>>,
}

impl PolyNexus {
    pub fn new(cfg: PolyNexusConfig, ts: Transys, results: MpMcResult) -> Self {
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
            ctrl: crate::EngineCtrl::default(),
            results,
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

    fn spawn_worker(
        prop: usize,
        cfg: IC3Config,
        ts: Transys,
        tx: mpsc::Sender<WorkerMsg>,
        p_stop: Arc<AtomicBool>,
    ) -> JoinHandle<()> {
        thread::spawn(move || {
            set_max_level(LevelFilter::Warn);
            if p_stop.load(Ordering::Relaxed) {
                return;
            }
            let mut ic3 = IC3::new(cfg, ts, VarSymbols::default());
            // Forward per-frame progress reports from IC3 to the main thread.
            let tx_progress = tx.clone();
            ic3.add_tracer(Box::new(PropTracerBridge {
                prop,
                tx: tx_progress,
            }));
            let result = ic3.check();
            let _ = tx.send(WorkerMsg::Done {
                prop,
                result,
                ic3: Box::new(ic3),
            });
        })
    }

    fn run(&mut self) -> MpMcResult {
        let num_workers = self.num_workers();
        let presets = ic3_presets();
        let num_props = self.ts.bad.len();
        let mut sched = Scheduler::new(num_props, presets);
        let (tx, rx) = mpsc::channel::<WorkerMsg>();
        let mut joins: Vec<JoinHandle<()>> = Vec::new();
        // Track per-prop unknown bound seen so far — only emit increasing values.
        let mut unknown_bound: Vec<Option<usize>> = vec![None; num_props];

        // Seed the initial wave of workers (up to num_workers in flight).
        while joins.len() < num_workers {
            match sched.next() {
                Some((prop, cfg)) => {
                    let p_stop = sched.prop_stop(prop);
                    let j = Self::spawn_worker(prop, cfg, self.ts.clone(), tx.clone(), p_stop);
                    joins.push(j);
                }
                None => break,
            }
        }

        loop {
            if self.ctrl.is_terminated() {
                for p in 0..num_props {
                    sched.prop_stops[p].store(true, Ordering::Relaxed);
                }
                break;
            }

            // Block until a message arrives; tx is still alive in this scope so
            // Disconnected only happens when all workers have exited.
            let msg = match rx.recv() {
                Ok(m) => m,
                Err(_) => break,
            };

            match msg {
                WorkerMsg::Progress { prop, result } => {
                    if !sched.resolved[prop] {
                        self.merge_and_trace(prop, result, &mut unknown_bound);
                    }
                }

                WorkerMsg::Done { prop, result, ic3 } => {
                    sched.worker_done(prop);

                    if !sched.resolved[prop] {
                        if !result.is_unknown() {
                            // Definitive answer — resolve and record.
                            sched.resolve(prop);
                            self.results[prop] = result;
                            self.tracer.trace_res(Some(prop), result);
                            self.ic3s[prop] = Some(ic3);
                        } else {
                            // Still unknown — merge bound, then spawn next preset
                            // for that property (keeps workers busy).
                            self.merge_and_trace(prop, result, &mut unknown_bound);
                            if let Some((next_prop, next_cfg)) = sched.next() {
                                let p_stop = sched.prop_stop(next_prop);
                                let j = Self::spawn_worker(
                                    next_prop,
                                    next_cfg,
                                    self.ts.clone(),
                                    tx.clone(),
                                    p_stop,
                                );
                                joins.push(j);
                            }
                        }
                    }

                    if sched.all_resolved() {
                        break;
                    }
                }
            }
        }

        // Stop any still-running workers and wait for them.
        for p in 0..num_props {
            sched.prop_stops[p].store(true, Ordering::Relaxed);
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
        self.tracer.trace_res(Some(prop), merged);
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
    fn trace_res(&mut self, _prop: Option<usize>, res: McResult) {
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
        todo!()
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn get_ctrl(&self) -> EngineCtrl {
        self.ctrl.clone()
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
