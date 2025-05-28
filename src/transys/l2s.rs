use super::Transys;
use crate::transys::TransysIf;
use logic_form::LitVec;
use std::iter::once;

impl Transys {
    pub fn l2s(&self) -> Self {
        let mut l2s = self.clone();
        let mut nls = Vec::new();
        for _ in self.latch.iter() {
            let nl = l2s.new_var();
            nls.push(nl);
            l2s.add_latch(nl, None, nl.lit());
        }
        let mut eqs = Vec::new();
        let mut eqns = Vec::new();
        for (l, nl) in self.latch.iter().zip(nls.iter()) {
            eqs.push(l2s.rel.new_xnor(l.lit(), nl.lit()));
            eqns.push(l2s.rel.new_xnor(self.next(l.lit()), nl.lit()));
        }
        let eq = l2s.rel.new_and(eqs);
        let eqn = l2s.rel.new_and(eqns);
        let encounter = l2s.new_var();
        let encounter_next = l2s.rel.new_or([eq, encounter.lit()]);
        l2s.add_latch(encounter, Some(false), encounter_next);
        let mut jlns = Vec::new();
        for &j in self.justice.iter().chain(self.fairness.iter()) {
            let jl = l2s.new_var();
            let jln = l2s.rel.new_and([encounter_next, j]);
            let jln = l2s.rel.new_or([jl.lit(), jln]);
            jlns.push(jln);
            l2s.add_latch(jl, Some(false), jln);
        }
        l2s.bad = LitVec::from([l2s.rel.new_and(jlns.into_iter().chain(once(eqn)))]);
        l2s.justice.clear();
        l2s.fairness.clear();
        l2s
    }
}
