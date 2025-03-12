use crate::IC3;
use logic_form::{Clause, Lemma};
use satif::Satif;
use satif_minisat::Solver;
use std::ops::Deref;
use transys::Transys;

pub fn verify_invariant(ts: &Transys, invariants: &[Lemma]) -> bool {
    let mut solver = Solver::new();
    solver.new_var_to(ts.max_var);
    for cls in ts.trans.iter() {
        solver.add_clause(cls)
    }
    for lemma in invariants {
        solver.add_clause(&!lemma.deref());
    }
    for c in ts.constraints.iter() {
        solver.add_clause(&Clause::from([*c]));
    }
    if solver.solve(&[ts.bad]) {
        return false;
    }
    for lemma in invariants {
        let mut assump = ts.constraints.clone();
        assump.extend_from_slice(&[ts.bad]);
        if solver.solve(&ts.cube_next(lemma)) {
            return false;
        }
    }
    true
}

impl IC3 {
    pub fn verify(&mut self) {
        let invariants = self.frame.invariant();
        if !verify_invariant(&self.ts, &invariants) {
            panic!("invariant varify failed");
        }
        if self.options.verbose > 0 {
            println!(
                "inductive invariant verified with {} lemmas!",
                invariants.len()
            );
        }
    }
}
