use crate::{
    Engine, Witness,
    config::Options,
    transys::{Transys, TransysIf, nodep::NoDepTransys, unroll::TransysUnroll},
};
use log::info;
use logic_form::LitVec;
use satif::Satif;
use std::time::Duration;

pub struct BMC {
    uts: TransysUnroll<NoDepTransys>,
    options: Options,
    solver: Box<dyn Satif>,
}

impl BMC {
    pub fn new(options: Options, ts: Transys) -> Self {
        let mut ts = ts.remove_dep();
        ts.assert_constraint();
        ts.simplify();
        let uts = TransysUnroll::new(&ts);
        let mut solver: Box<dyn Satif> = if options.bmc.bmc_kissat {
            Box::new(kissat::Solver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
        ts.load_init(solver.as_mut());
        Self {
            uts,
            options,
            solver,
        }
    }

    pub fn reset_solver(&mut self) {
        self.solver = if self.options.bmc.bmc_kissat {
            Box::new(kissat::Solver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
        self.uts.ts.load_init(self.solver.as_mut());
    }
}

impl Engine for BMC {
    fn check(&mut self) -> Option<bool> {
        let step = self.options.step as usize;
        let bmc_max_k = self.options.bmc.bmc_max_k;
        for k in (step - 1..=bmc_max_k).step_by(step) {
            self.uts.unroll_to(k);
            let last_bound = if self.options.bmc.bmc_kissat {
                self.reset_solver();
                0
            } else {
                k + 1 - step
            };
            for s in last_bound..=k {
                self.uts.load_trans(self.solver.as_mut(), s, true);
            }
            let mut assump = self.uts.lits_next(&self.uts.ts.bad.cube(), k);
            if self.options.bmc.bmc_kissat {
                for b in assump.iter() {
                    self.solver.add_clause(&[*b]);
                }
                assump.clear();
            }
            info!("bmc depth: {k}");
            let r = if let Some(limit) = self.options.bmc.time_limit {
                let Some(r) = self
                    .solver
                    .solve_with_limit(&assump, Duration::from_secs(limit))
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

            // for s in last_bound..=k {
            //     solver.add_clause(&[!self.uts.lit_next(self.uts.ts.bad, s)]);
            // }
        }
        info!("bmc reached bound {bmc_max_k}, stopping search");
        None
    }

    fn witness(&mut self, _ts: &Transys) -> Witness {
        let mut wit = Witness::default();
        for l in self.uts.ts.latch() {
            let l = l.lit();
            if let Some(v) = self.solver.sat_value(l)
                && let Some(r) = self.uts.ts.restore(l.not_if(!v))
            {
                wit.init.push(r);
            }
        }
        for k in 0..=self.uts.num_unroll {
            let mut w = LitVec::new();
            for l in self.uts.ts.input() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl)
                    && let Some(r) = self.uts.ts.restore(l.not_if(!v))
                {
                    w.push(r);
                }
            }
            wit.wit.push(w);
        }
        wit
    }
}
