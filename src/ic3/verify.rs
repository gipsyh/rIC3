use crate::{
    ic3::IC3,
    transys::{TransysCtx, TransysIf},
};
use cadical::Solver;
use log::{error, info};
use logicrs::{LitVec, Var, satif::Satif};

#[allow(unused)]
pub fn verify_invariant(ts: &TransysCtx, mut invariants: Vec<LitVec>, is_init: Var) -> bool {
    let mut solver = Solver::new();
    ts.load_trans(&mut solver, true);
    ts.load_init(&mut solver);
    for lemma in invariants.iter() {
        if solver.solve(lemma) {
            return false;
        }
    }
    let mut solver = Solver::new();
    ts.load_trans(&mut solver, true);
    invariants.push(LitVec::from([is_init.lit()]));
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
        let num_inv = invariants.len();
        if !verify_invariant(&self.tsctx, invariants, self.rst.init_var()) {
            error!("invariant varify failed");
            panic!();
        }
        info!("inductive invariant verified with {num_inv} lemmas!");
    }
}
