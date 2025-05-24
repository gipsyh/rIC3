use super::Solver;
use logic_form::{Lit, LitVec};
use rand::seq::SliceRandom;
use satif::Satif;

impl Solver {
    #[inline]
    pub fn minimal_pred(
        &mut self,
        inputs: &[Lit],
        latchs: &[Lit],
        target_constrain: &LitVec,
    ) -> Option<LitVec> {
        let assump = LitVec::from_iter(inputs.iter().chain(latchs.iter()).copied());
        if self.solve(&assump, vec![target_constrain.clone()]) {
            return None;
        }
        Some(
            latchs
                .iter()
                .filter(|l| self.unsat_has(**l))
                .copied()
                .collect(),
        )
    }

    #[allow(unused)]
    pub fn get_pred(
        &mut self,
        solver: &impl Satif,
        target: &[Lit],
        strengthen: bool,
    ) -> (LitVec, LitVec) {
        let mut cls: LitVec = target.into();
        cls.extend_from_slice(&self.ts.constraints);
        if cls.is_empty() {
            return (LitVec::new(), LitVec::new());
        }
        let cls = !cls;
        let mut inputs = LitVec::new();
        for input in self.ts.inputs.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        self.set_domain(cls.iter().cloned());
        let mut latchs = LitVec::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            if self.domain.has(lit.var())
                && let Some(v) = solver.sat_value(lit)
            {
                latchs.push(lit.not_if(!v));
            }
        }
        for _ in 0.. {
            if latchs.is_empty() {
                break;
            }
            latchs.shuffle(&mut self.rng);
            let olen = latchs.len();
            latchs = self.minimal_pred(&inputs, &latchs, &cls).unwrap();
            if latchs.len() == olen || !strengthen {
                break;
            }
        }
        self.unset_domain();
        (latchs, inputs)
    }
}
