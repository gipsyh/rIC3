use crate::gipsat::{ClauseKind, DagCnfSolver, cdb::CRef};
use giputils::gvec::Gvec;
use logicrs::{Lit, LitMap, Var};
use std::mem::take;

#[derive(Clone)]
pub struct Eqc {
    eq: LitMap<Lit>,
}

impl Eqc {
    pub fn reserve(&mut self, var: Var) {
        while self.eq.max_index() < var {
            let x = Var(Into::<u32>::into(self.eq.max_index()) + 1);
            self.eq.reserve(x);
            let x = x.lit();
            self.eq[x] = x;
            self.eq[!x] = !x;
        }
    }

    pub fn get_eq(&mut self, x: Lit) -> Lit {
        if self.eq[x] != x {
            let p = self.get_eq(self.eq[x]);
            self.eq[x] = p;
            self.eq[!x] = !p;
        }
        self.eq[x]
    }

    pub fn add_eq(&mut self, x: Lit, y: Lit) {
        let mut xp = self.get_eq(x);
        let mut yp = self.get_eq(y);
        if xp == yp {
            return;
        }
        if xp.var() > yp.var() {
            (xp, yp) = (yp, xp);
        }
        self.eq[yp] = xp;
        self.eq[!yp] = !xp;
    }
}

impl Default for Eqc {
    fn default() -> Self {
        let mut eq = LitMap::new();
        eq.reserve(Var::CONST);
        eq[Lit::constant(true)] = Lit::constant(true);
        eq[Lit::constant(false)] = Lit::constant(false);
        Self { eq }
    }
}

impl DagCnfSolver {
    fn clean_eq_inner(&mut self, mut clauses: Gvec<CRef>, kind: ClauseKind) -> Gvec<CRef> {
        let mut i = 0;
        'm: while i < clauses.len() {
            let cid = clauses[i];
            let cls = self.cdb.get(cid);
            if cls.slice().iter().any(|&l| self.eqc.get_eq(l) != l) {
                let mut cls = cls.litvec();
                self.detach_clause(cid);
                for j in 0..cls.len() {
                    let eq = self.eqc.get_eq(cls[j]);
                    if eq != cls[j] {
                        cls[j] = eq;
                    }
                }
                self.add_clause_inner(&cls, kind);
                clauses.swap_remove(i);
                continue 'm;
            }
            i += 1;
        }
        clauses
    }

    pub fn clean_eq(&mut self) {
        let lemmas = take(&mut self.cdb.lemmas);
        let lemmas = self.clean_eq_inner(lemmas, ClauseKind::Lemma);
        self.cdb.lemmas.extend(lemmas);
        let learnt = take(&mut self.cdb.learnt);
        let learnt = self.clean_eq_inner(learnt, ClauseKind::Learnt);
        self.cdb.learnt.extend(learnt);
        let trans = take(&mut self.cdb.trans);
        let trans = self.clean_eq_inner(trans, ClauseKind::Trans);
        self.cdb.trans.extend(trans);
    }
}
