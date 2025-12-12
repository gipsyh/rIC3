use crate::{
    ic3::IC3,
    transys::{TransysCtx, TransysIf},
};
use log::{error, info};
use logicrs::{LitVec, satif::Satif};

#[allow(unused)]
pub fn verify_invariant(ts: &TransysCtx, mut invariants: &[LitVec]) -> bool {
    let mut solver = cadical::CaDiCaL::new();
    ts.load_trans(&mut solver, true);
    ts.load_init(&mut solver);
    for lemma in invariants.iter() {
        if solver.solve(lemma) {
            return false;
        }
    }
    let mut solver = cadical::CaDiCaL::new();
    ts.load_trans(&mut solver, true);
    for lemma in invariants.iter() {
        solver.add_clause(&!lemma);
    }
    if solver.solve(&ts.bad.cube()) {
        return false;
    }
    for lemma in invariants.iter() {
        if solver.solve(&ts.lits_next(lemma)) {
            return false;
        }
    }
    true
}

impl IC3 {
    #[allow(unused)]
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
}
