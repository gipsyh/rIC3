use super::{IC3, proofoblig::ProofObligation};
use crate::transys::{Transys, TransysCtx, TransysIf, unroll::TransysUnroll};
use cadical::Solver;
use log::{error, info};
use logicrs::{LitVec, satif::Satif};

pub fn verify_invariant(ts: &TransysCtx, invariants: &[LitVec]) -> bool {
    let mut solver = Solver::new();
    ts.load_trans(&mut solver, true);
    ts.load_init(&mut solver);
    for lemma in invariants {
        if solver.solve(lemma) {
            return false;
        }
    }
    let mut solver = Solver::new();
    ts.load_trans(&mut solver, true);
    for lemma in invariants {
        solver.add_clause(&!lemma);
    }
    if solver.solve(&ts.bad.cube()) {
        return false;
    }
    for lemma in invariants {
        if solver.solve(&ts.lits_next(lemma)) {
            return false;
        }
    }
    true
}

impl IC3 {
    pub(super) fn verify(&mut self) {
        if !self.cfg.certify {
            return;
        }
        let invariants = self.frame.invariant();
        if !verify_invariant(&self.tsctx, &invariants) {
            error!("invariant varify failed");
            panic!();
        }
        info!(
            "inductive invariant verified with {} lemmas!",
            invariants.len()
        );
    }

    fn check_witness_with_constrain<S: Satif + ?Sized>(
        &mut self,
        solver: &mut S,
        uts: &TransysUnroll<Transys>,
        constraint: &LitVec,
    ) -> bool {
        let mut assumps = LitVec::new();
        for k in 0..=uts.num_unroll {
            assumps.extend_from_slice(&uts.lits_next(constraint, k));
        }
        assumps.extend(uts.lits_next(&uts.ts.bad, uts.num_unroll));
        solver.solve(&assumps)
    }

    pub(super) fn check_witness_by_bmc(&mut self, b: ProofObligation) -> Option<LitVec> {
        let mut uts = TransysUnroll::new(&self.ts);
        uts.unroll_to(b.depth);
        let mut solver: Box<dyn Satif> = Box::new(cadical::Solver::new());
        for k in 0..=b.depth {
            uts.load_trans(solver.as_mut(), k, false);
        }
        uts.ts.load_init(solver.as_mut());
        let mut cst: LitVec = uts.ts.constraint().collect();
        if self.check_witness_with_constrain(solver.as_mut(), &uts, &cst) {
            info!("witness checking passed");
            self.bmc_solver = Some((solver, uts));
            None
        } else {
            let mut i = 0;
            while i < cst.len() {
                if self.abs_cst.contains(&cst[i]) {
                    i += 1;
                    continue;
                }
                let mut drop = cst.clone();
                drop.remove(i);
                if self.check_witness_with_constrain(solver.as_mut(), &uts, &drop) {
                    i += 1;
                } else {
                    cst = drop;
                }
            }
            cst.retain(|l| !self.abs_cst.contains(l));
            assert!(!cst.is_empty());
            Some(cst)
        }
    }
}
