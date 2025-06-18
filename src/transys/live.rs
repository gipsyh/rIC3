use super::Transys;
use crate::transys::TransysIf;
use log::warn;
use logicrs::{LitVec, VarVMap};
use std::{iter::once, mem::take};

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
        for &j in self.justice.iter() {
            let jl = l2s.new_var();
            let jln = l2s.rel.new_and([encounter_next, j]);
            let jln = l2s.rel.new_or([jl.lit(), jln]);
            jlns.push(jln);
            l2s.add_latch(jl, Some(false), jln);
        }
        l2s.bad = LitVec::from([l2s.rel.new_and(jlns.into_iter().chain(once(eqn)))]);
        l2s.justice.clear();
        l2s
    }

    pub fn check_liveness_and_l2s(self, _rst: &mut VarVMap) -> Self {
        if !self.bad.is_empty() {
            assert!(self.justice.is_empty());
            self
        } else {
            warn!("liveness property found, converting to safety property");
            self.l2s()
        }
    }

    pub fn normalize_justice(&mut self) {
        assert!(!self.justice.is_empty());
        if self.justice.len() == 1 {
            return;
        }
        let justice = take(&mut self.justice);
        let mut ljs = Vec::new();
        let mut ljns = Vec::new();
        for &j in justice.iter() {
            let lj = self.new_var();
            ljs.push(lj);
            let ljn = self.rel.new_or([lj.lit(), j]);
            ljns.push(ljn);
        }
        let accept = self.rel.new_and(ljns.clone());
        let ni = self.new_var();
        self.add_input(ni);
        let reset = self.rel.new_or([ni.lit(), accept]);
        for (&lj, &ljn) in ljs.iter().zip(ljns.iter()) {
            let ljn = self.rel.new_and([ljn, !reset]);
            self.add_latch(lj, Some(false), ljn);
        }
        self.justice.push(accept);
    }
}
