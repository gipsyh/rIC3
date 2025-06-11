use crate::{
    Engine, Witness,
    config::Config,
    transys::{Transys, TransysIf, nodep::NoDepTransys, unroll::TransysUnroll},
};
use log::info;
use logic_form::{LitVec, VarVMap};
use satif::Satif;
use std::time::Duration;

pub struct BMC {
    uts: TransysUnroll<NoDepTransys>,
    cfg: Config,
    solver: Box<dyn Satif>,
    solver_k: usize,
    rst: VarVMap,
}

impl BMC {
    pub fn new(cfg: Config, mut ts: Transys) -> Self {
        let mut rst = VarVMap::new_self_map(ts.max_var());
        ts = ts.check_liveness_and_l2s(&mut rst);
        let mut ts = ts.remove_dep();
        ts.assert_constraint();
        if !cfg.preproc.no_preproc {
            ts.simplify(&mut rst);
        }
        let uts = TransysUnroll::new(&ts);
        let mut solver: Box<dyn Satif> = if cfg.bmc.bmc_kissat {
            Box::new(kissat::Solver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
        ts.load_init(solver.as_mut());
        Self {
            uts,
            cfg,
            solver,
            solver_k: 0,
            rst,
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
        self.solver = if self.cfg.bmc.bmc_kissat {
            Box::new(kissat::Solver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
        self.uts.ts.load_init(self.solver.as_mut());
        for i in 0..self.solver_k {
            self.uts.load_trans(self.solver.as_mut(), i, true);
        }
    }
}

impl Engine for BMC {
    fn check(&mut self) -> Option<bool> {
        let step = self.cfg.step as usize;
        for k in (self.cfg.start..=self.cfg.end).step_by(step) {
            self.uts.unroll_to(k);
            self.load_trans_to(k);
            let mut assump = self.uts.lits_next(&self.uts.ts.bad.cube(), k);
            if self.cfg.bmc.bmc_kissat {
                for b in assump.iter() {
                    self.solver.add_clause(&[*b]);
                }
                assump.clear();
            }
            info!("bmc depth: {k}");
            let r = if let Some(limit) = self.cfg.bmc.time_limit {
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
                info!("bmc found counter-example in depth {k}");
                return Some(false);
            }
            if self.cfg.bmc.bmc_kissat {
                self.reset_solver();
            }
        }
        info!("bmc reached bound {}, stopping search", self.cfg.end);
        None
    }

    fn witness(&mut self) -> Witness {
        let mut wit = Witness::default();
        for k in 0..=self.uts.num_unroll {
            let mut w = LitVec::new();
            for l in self.uts.ts.input() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl)
                    && let Some(r) = self.rst.lit_map(l.not_if(!v))
                {
                    w.push(r);
                }
            }
            wit.input.push(w);
            let mut w = LitVec::new();
            for l in self.uts.ts.latch() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl)
                    && let Some(r) = self.rst.lit_map(l.not_if(!v))
                {
                    w.push(r);
                }
            }
            wit.state.push(w);
        }
        wit
    }
}
