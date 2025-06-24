use crate::gipsat::DagCnfSolver;
use logicrs::{Lit, LitVec, satif::Satif};

impl DagCnfSolver {
    pub fn minimal_premise(
        &mut self,
        assump: &[Lit],
        premise: &[Lit],
        consequent: &[Lit],
    ) -> Option<LitVec> {
        let assump = LitVec::from_iter(assump.iter().chain(premise.iter()).copied());
        if self.solve_with_constraint(&assump, vec![LitVec::from(consequent)]) {
            return None;
        }
        Some(
            premise
                .iter()
                .filter(|l| self.unsat_has(**l))
                .copied()
                .collect(),
        )
    }
}
