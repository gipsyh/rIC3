use crate::{frames::Lemma, solver::Ic3Solver, Ic3};
use cadical::SatResult;
use std::ops::Deref;

impl Ic3 {
    fn verify_invariant(&mut self, invariants: &[Lemma]) -> bool {
        let mut solver = Ic3Solver::new(&self.model, 1);
        for lemma in invariants {
            solver.add_clause(&!lemma.deref());
        }
        if let SatResult::Sat(_) = solver.solve(&self.model.bad) {
            return false;
        }
        for lemma in invariants {
            if let SatResult::Sat(_) = solver.solve(&self.model.cube_next(lemma)) {
                return false;
            }
        }
        true
    }

    pub fn verify(&mut self) -> bool {
        let invariant = self
            .frames
            .iter()
            .position(|frame| frame.is_empty())
            .unwrap();
        let mut invariants = Vec::new();
        for i in invariant..self.frames.len() {
            for cube in self.frames[i].iter() {
                invariants.push(cube.clone());
            }
        }
        if !self.verify_invariant(&invariants) {
            println!("invariant varify failed");
            return false;
        }
        println!(
            "inductive invariant verified with {} lemmas!",
            invariants.len()
        );
        true
    }
}
