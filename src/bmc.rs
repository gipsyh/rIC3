use crate::{
    options::Options,
    transys::{unroll::TransysUnroll, Transys},
    witness_encode, Engine,
};
use aig::Aig;
use logic_form::LitVec;
use satif::Satif;
use std::time::Duration;

pub struct BMC {
    uts: TransysUnroll,
    options: Options,
    solver: Box<dyn Satif>,
}

impl BMC {
    pub fn new(options: Options, ts: Transys) -> Self {
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
        for k in (step - 1..).step_by(step) {
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
            if self.options.verbose > 0 {
                println!("bmc depth: {k}");
            }
            let r = if let Some(limit) = self.options.bmc.time_limit {
                let Some(r) = self
                    .solver
                    .solve_with_limit(&assump, Duration::from_secs(limit))
                else {
                    if self.options.verbose > 0 {
                        println!("bmc solve timeout in depth {k}");
                    }
                    continue;
                };
                r
            } else {
                self.solver.solve(&assump)
            };
            if r {
                if self.options.verbose > 0 {
                    println!("bmc found cex in depth {k}");
                }
                return Some(false);
            }
            // for s in last_bound..=k {
            //     solver.add_clause(&[!self.uts.lit_next(self.uts.ts.bad, s)]);
            // }
        }
        unreachable!();
    }

    fn witness(&mut self, aig: &Aig) -> String {
        let mut wit = vec![LitVec::new()];
        for l in self.uts.ts.latchs.iter() {
            let l = l.lit();
            if let Some(v) = self.solver.sat_value(l) {
                wit[0].push(self.uts.ts.restore(l.not_if(!v)));
            }
        }
        for k in 0..=self.uts.num_unroll {
            let mut w = LitVec::new();
            for l in self.uts.ts.inputs.iter() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl) {
                    w.push(self.uts.ts.restore(l.not_if(!v)));
                }
            }
            wit.push(w);
        }
        witness_encode(aig, &wit)
    }
}
