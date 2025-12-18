use crate::{
    Engine, Witness,
    config::{EngineConfigBase, PreprocConfig},
    tracer::{Tracer, TracerIf},
    transys::{Transys, TransysIf, certify::Restore, nodep::NoDepTransys, unroll::TransysUnroll},
};
use clap::Args;
use log::info;
use logicrs::satif::Satif;
use rand::{Rng, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};
use std::{ops::Deref, time::Duration};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct BMCConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,

    /// per-step time limit (applies to each BMC step, not the overall solver run).
    /// The overall `time_limit` option sets the total time limit for the entire solver run.
    #[arg(long = "step-time-limit")]
    pub step_time_limit: Option<u64>,

    /// use kissat solver in bmc, otherwise cadical
    #[arg(long = "kissat", default_value_t = false)]
    pub kissat: bool,

    /// dynamic step
    #[arg(long = "dyn-step", default_value_t = false)]
    pub dyn_step: bool,
}

impl Deref for BMCConfig {
    type Target = EngineConfigBase;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

pub struct BMC {
    ots: Transys,
    uts: TransysUnroll<NoDepTransys>,
    cfg: BMCConfig,
    solver: Box<dyn Satif>,
    solver_k: usize,
    rst: Restore,
    step: usize,
    rng: StdRng,
    tracer: Tracer,
}

impl BMC {
    pub fn new(cfg: BMCConfig, mut ts: Transys) -> Self {
        let ots = ts.clone();
        ts.compress_bads();
        let mut rng = StdRng::seed_from_u64(cfg.rseed);
        let rst = Restore::new(&ts);
        let (ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        let mut ts = ts.remove_dep();
        ts.assert_constraint();
        if cfg.preproc.preproc {
            ts.simplify(&mut rst);
        }
        let uts = TransysUnroll::new(&ts);
        let mut solver: Box<dyn Satif> = if cfg.kissat {
            Box::new(kissat::Kissat::new())
        } else {
            Box::new(cadical::CaDiCaL::new())
        };
        solver.set_seed(rng.random());
        ts.load_init(solver.as_mut());
        let step = if cfg.dyn_step {
            (10_000_000 / (*ts.max_var() as usize + ts.rel.clauses().len())).max(1)
        } else {
            cfg.step as usize
        };
        Self {
            ots,
            uts,
            step,
            cfg,
            solver,
            solver_k: 0,
            rst,
            rng,
            tracer: Tracer::new(),
        }
    }

    pub fn load_trans_to(&mut self, k: usize) {
        while self.solver_k < k + 1 {
            self.uts
                .load_trans(self.solver.as_mut(), self.solver_k, true);
            self.solver_k += 1;
        }
    }

    pub fn reset_solver(&mut self) {
        self.solver = if self.cfg.kissat {
            Box::new(kissat::Kissat::new())
        } else {
            Box::new(cadical::CaDiCaL::new())
        };
        self.solver.set_seed(self.rng.random());
        self.uts.ts.load_init(self.solver.as_mut());
        for i in 0..self.solver_k {
            self.uts.load_trans(self.solver.as_mut(), i, true);
        }
    }
}

impl Engine for BMC {
    fn check(&mut self) -> Option<bool> {
        for k in (self.cfg.start..=self.cfg.end).step_by(self.step) {
            self.uts.unroll_to(k);
            self.load_trans_to(k);
            let mut assump = self.uts.lits_next(&self.uts.ts.bad, k);
            if self.cfg.kissat {
                for b in assump.iter() {
                    self.solver.add_clause(&[*b]);
                }
                assump.clear();
            }
            let r = if let Some(limit) = self.cfg.step_time_limit {
                let Some(r) =
                    self.solver
                        .solve_with_limit(&assump, vec![], Duration::from_secs(limit))
                else {
                    info!("bmc solve timeout in depth {k}");
                    continue;
                };
                r
            } else {
                self.solver.solve(&assump)
            };
            if r {
                self.tracer.trace_res(crate::McResult::Unsafe(k));
                return Some(false);
            }
            self.tracer.trace_res(crate::McResult::Unknown(Some(k)));
            if self.cfg.kissat {
                self.reset_solver();
            }
        }
        info!("bmc reached bound {}, stopping search", self.cfg.end);
        None
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn witness(&mut self) -> Witness {
        let mut wit = self.uts.witness(self.solver.as_ref());
        wit = wit.map(|l| self.rst.restore(l));
        for s in wit.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        wit.exact_state(&self.ots);
        wit
    }
}
