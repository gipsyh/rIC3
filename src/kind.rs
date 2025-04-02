use crate::{
    Engine, Proof, Witness,
    options::Options,
    transys::{Transys, TransysIf, nodep::NoDepTransys, unroll::TransysUnroll},
};
use logic_form::{LitVec, Var};
use satif::Satif;

pub struct Kind {
    uts: TransysUnroll<NoDepTransys>,
    options: Options,
    solver: Box<dyn Satif>,
}

impl Kind {
    pub fn new(options: Options, ts: Transys) -> Self {
        let mut ts = ts.remove_dep();
        ts.assert_constraint();
        ts.simplify();
        let uts = if options.kind.simple_path {
            TransysUnroll::new_with_simple_path(&ts)
        } else {
            TransysUnroll::new(&ts)
        };
        let solver: Box<dyn Satif> = if options.kind.kind_kissat {
            Box::new(kissat::Solver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
        Self {
            uts,
            options,
            solver,
        }
    }

    // pub fn check_in_depth(&mut self, depth: usize) -> bool {
    //     println!("{}", self.options.model);
    //     assert!(depth > 0);
    //     let mut solver = kissat::Solver::new();
    //     self.uts.unroll_to(depth);
    //     for k in 0..=depth {
    //         self.uts.load_trans(&mut solver, k, true);
    //     }
    //     for k in 0..depth {
    //         solver.add_clause(&!self.uts.lits_next(&self.uts.ts.bad, k));
    //         self.load_pre_lemmas(&mut solver, k);
    //     }
    //     for b in self.uts.lits_next(&self.uts.ts.bad, depth).iter() {
    //         solver.add_clause(&[*b]);
    //     }
    //     println!("kind depth: {depth}");
    //     if !solver.solve(&[]) {
    //         println!("kind proofed in depth {depth}");
    //         return true;
    //     }
    //     false
    // }

    pub fn reset_solver(&mut self) {
        self.solver = if self.options.kind.kind_kissat {
            Box::new(kissat::Solver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
    }
}

impl Engine for Kind {
    fn check(&mut self) -> Option<bool> {
        let step = self.options.step as usize;
        self.uts.load_trans(self.solver.as_mut(), 0, true);
        for k in (step..).step_by(step) {
            let bmc_k = k - 1;
            let start = k + 1 - step;
            if self.options.kind.kind_kissat {
                self.reset_solver();
                for i in 0..start {
                    self.uts.load_trans(self.solver.as_mut(), i, true);
                }
                if bmc_k >= step {
                    for i in 0..=bmc_k - step {
                        self.solver
                            .add_clause(&!self.uts.lits_next(&self.uts.ts.bad.cube(), i));
                    }
                }
            }
            self.uts.unroll_to(bmc_k);
            for i in start..=bmc_k {
                self.uts.load_trans(self.solver.as_mut(), i, true);
            }
            if !self.options.kind.no_bmc {
                let mut assump: LitVec = self.uts.ts.init().collect();
                assump.extend_from_slice(&self.uts.lits_next(&self.uts.ts.bad.cube(), bmc_k));
                if self.options.verbose > 0 {
                    println!("kind bmc depth: {bmc_k}");
                }
                if self.solver.solve(&assump) {
                    if self.options.verbose > 0 {
                        println!("bmc found cex in depth {bmc_k}");
                    }
                    return Some(false);
                }
            }
            for i in bmc_k + 1 - step..=bmc_k {
                self.solver
                    .add_clause(&!self.uts.lits_next(&self.uts.ts.bad.cube(), i));
            }
            self.uts.unroll_to(k);
            self.uts.load_trans(self.solver.as_mut(), k, true);
            if self.options.verbose > 0 {
                println!("kind depth: {k}");
            }
            let res = if self.options.kind.kind_kissat {
                for l in self.uts.lits_next(&self.uts.ts.bad.cube(), k) {
                    self.solver.add_clause(&[l]);
                }
                self.solver.solve(&[])
            } else {
                self.solver
                    .solve(&self.uts.lits_next(&self.uts.ts.bad.cube(), k))
            };
            if !res {
                println!("k-induction proofed in depth {k}");
                return Some(true);
            }
        }
        unreachable!();
    }

    fn proof(&mut self, ts: &Transys) -> Proof {
        if self.options.kind.simple_path {
            //TODO: support certifaiger with simple path constraint
            panic!("k-induction with simple path constraint not support certifaiger");
        }
        let mut proof = ts.clone();
        proof.constraint = LitVec::from([proof.rel.new_and(proof.constraint.into_iter())]);
        let ni = proof.input.len();
        let nl = proof.latch.len();
        let nc = proof.constraint.len();
        let k = self.uts.num_unroll;
        for _ in 1..k {
            proof.merge(ts);
        }
        let inputs = proof.input.clone();
        proof.input.truncate(ni);
        let latchs = proof.latch.clone();
        proof.latch.truncate(nl);
        // let mut bads: Vec<AigEdge> = certifaiger
        //     .bads
        //     .iter()
        //     .chain(certifaiger.outputs.iter())
        //     .copied()
        //     .collect();
        // certifaiger.bads.clear();
        // certifaiger.outputs.clear();
        // let mut constrains = Vec::new();
        proof.constraint.truncate(nc);
        // for i in 0..k {
        //     bads[i] = certifaiger.new_or_node(bads[i], !constrains[i]);
        // }
        // let sum = inputs.len() + latchs.len();
        let mut aux_latchs: Vec<Var> = Vec::new();
        for i in 0..k {
            let input = proof.new_var();
            aux_latchs.push(input.into());
            //     let (next, init) = if i == 0 {
            //         (input.into(), Some(true))
            //     } else {
            //         (aux_latchs[i - 1], Some(false))
            //     };
            //     certifaiger.add_latch(input, next, init);
        }
        // for i in 1..k {
        //     for j in 0..ni {
        //         certifaiger.add_latch(inputs[j + i * ni], inputs[j + (i - 1) * ni].into(), None);
        //     }
        //     for j in 0..nl {
        //         certifaiger.add_latch(
        //             latchs[j + i * nl].input,
        //             latchs[j + (i - 1) * nl].input.into(),
        //             None,
        //         );
        //     }
        // }
        // for i in 0..k {
        //     let al = aux_latchs[i];
        //     let p = certifaiger.new_imply_node(al, !bads[i]);
        //     certifaiger.bads.push(!p);
        // }
        // for i in 1..k {
        //     let al = aux_latchs[i];
        //     let al_next = aux_latchs[i - 1];
        //     let p = certifaiger.new_imply_node(al, al_next);
        //     certifaiger.bads.push(!p);
        //     let mut eqs = Vec::new();
        //     let mut init = Vec::new();
        //     for j in 0..nl {
        //         if let Some(linit) = latchs[j].init {
        //             init.push(AigEdge::new(latchs[(i - 1) * nl + j].input, !linit))
        //         }
        //         eqs.push(certifaiger.new_eq_node(
        //             latchs[j + i * nl].next,
        //             latchs[j + (i - 1) * nl].input.into(),
        //         ));
        //     }
        //     let p = certifaiger.new_ands_node(eqs.into_iter());
        //     let p = certifaiger.new_imply_node(al, p);
        //     certifaiger.bads.push(!p);
        //     let init = certifaiger.new_ands_node(init.into_iter());
        //     let p = certifaiger.new_and_node(!al, al_next);
        //     let p = certifaiger.new_imply_node(p, init);
        //     certifaiger.bads.push(!p);
        // }
        // certifaiger.bads.push(!aux_latchs[0]);
        // let bads: Vec<AigEdge> = certifaiger
        //     .bads
        //     .iter()
        //     .chain(certifaiger.outputs.iter())
        //     .copied()
        //     .collect();
        // let bads = certifaiger.new_ors_node(bads.into_iter());
        // certifaiger.bads.clear();
        // certifaiger.outputs.clear();
        // certifaiger.outputs.push(bads);
        // assert!(certifaiger.inputs.len() + certifaiger.latchs.len() == sum + k);
        // certifaiger
        todo!();
    }

    fn witness(&mut self, _ts: &Transys) -> Witness {
        let mut wit = Witness::default();
        for l in self.uts.ts.latch() {
            let l = l.lit();
            if let Some(v) = self.solver.sat_value(l) {
                wit.init.push(self.uts.ts.restore(l.not_if(!v)));
            }
        }
        for k in 0..=self.uts.num_unroll {
            let mut w = LitVec::new();
            for l in self.uts.ts.input() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl) {
                    w.push(self.uts.ts.restore(l.not_if(!v)));
                }
            }
            wit.wit.push(w);
        }
        wit
    }
}
