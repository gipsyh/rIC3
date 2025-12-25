use crate::{
    Engine, McResult, McWitness,
    config::EngineConfigBase,
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    wltransys::{WlTransys, unroll::WlTransysUnroll},
};
use clap::Args;
use log::info;
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct WlBMCConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,
}

impl_config_deref!(WlBMCConfig);

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
        self.solver_k = self.uts.load_trans_to(&mut self.solver, self.solver_k, k);
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
        self.uts.compute_bad_id(&mut witness, &self.owts, &mut self.solver);
        McWitness::Wl(witness)
    }
}
