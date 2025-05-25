use super::Transys;
use crate::transys::TransysIf;
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
        for (l, nl) in self.latch.iter().zip(nls.iter()) {
            eqs.push(l2s.rel.new_xnor(l.lit(), nl.lit()));
        }
        let eq = l2s
            .rel
            .new_and(eqs.into_iter().chain(once(self.justice[0])));
        let encounter = l2s.new_var();
        let next = l2s.rel.new_or([eq, encounter.lit()]);
        l2s.add_latch(encounter, Some(false), next);
        assert!(l2s.fairness.is_empty());
        l2s.bad = l2s.rel.new_and([eq, encounter.lit()]);
        l2s.justice.clear();
        l2s.fairness.clear();
        l2s
    }
}
