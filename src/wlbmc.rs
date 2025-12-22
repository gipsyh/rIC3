use crate::{
    Engine, McResult, McWitness,
    config::EngineConfigBase,
    tracer::{Tracer, TracerIf},
    wltransys::{WlTransys, unroll::WlTransysUnroll},
};
use clap::Args;
use giputils::hash::GHashMap;
use log::info;
use serde::{Deserialize, Serialize};
use std::ops::Deref;

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct WlBMCConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,
}

impl Deref for WlBMCConfig {
    type Target = EngineConfigBase;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

pub struct WlBMC {
    cfg: WlBMCConfig,
    #[allow(unused)]
    owts: WlTransys,
    uts: WlTransysUnroll,
    solver: bitwuzla::Bitwuzla,
    solver_k: usize,
    tracer: Tracer,
}

impl WlBMC {
    pub fn new(cfg: WlBMCConfig, mut wts: WlTransys) -> Self {
        let owts = wts.clone();
        wts.compress_bads();
        let uts = WlTransysUnroll::new(wts);
        let mut solver = bitwuzla::Bitwuzla::new();
        for (l, i) in uts.ts.init.iter() {
            solver.assert(&l.teq(i));
        }
        Self {
            cfg,
            owts,
            uts,
            solver,
            solver_k: 0,
            tracer: Tracer::new(),
        }
    }

    pub fn load_trans_to(&mut self, k: usize) {
        while self.solver_k < k + 1 {
            for c in self.uts.ts.constraint.iter() {
                self.solver.assert(&self.uts.next(c, self.solver_k));
            }
            self.solver_k += 1;
        }
    }
}

impl Engine for WlBMC {
    fn check(&mut self) -> McResult {
        for k in (self.cfg.start..=self.cfg.end).step_by(self.cfg.step as usize) {
            self.uts.unroll_to(k);
            self.load_trans_to(k);
            let assump = self.uts.next(&self.uts.ts.bad[0], k);
            if self.solver.solve(&[assump]) {
                self.tracer.trace_res(crate::McResult::Unsafe(k));
                return McResult::Unsafe(k);
            }
            self.tracer.trace_res(crate::McResult::Unknown(Some(k)));
        }
        info!("bmc reached bound {}, stopping search", self.cfg.end);
        McResult::Unknown(Some(self.cfg.end))
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn witness(&mut self) -> McWitness {
        let mut witness = self.uts.witness(&mut self.solver);
        let mut cache = GHashMap::new();
        let mut ilmap = GHashMap::new();
        for i in self.owts.input.iter().chain(self.owts.latch.iter()) {
            ilmap.insert(i, self.uts.next(i, self.uts.num_unroll));
        }
        let bads: Vec<_> = self
            .owts
            .bad
            .iter()
            .map(|b| b.cached_apply(&|t| ilmap.get(t).cloned(), &mut cache))
            .collect();
        witness.bad_id = bads
            .into_iter()
            .position(|b| self.solver.sat_value(&b).is_some_and(|v| v.bool()))
            .unwrap();
        McWitness::Wl(witness)
    }
}
