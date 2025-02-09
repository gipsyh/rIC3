use super::{
    cdb::{CRef, CREF_NONE},
    Solver,
};
use giputils::gvec::Gvec;
use logic_form::{Lemma, LitMap, LitVec};
use std::mem::take;

pub struct Simplify {
    pub last_num_assign: u32,
    pub last_simplify: usize,
    pub lazy_remove: Vec<LitVec>,
    pub last_num_lemma: u32,
}

impl Default for Simplify {
    fn default() -> Self {
        Self {
            last_num_assign: 0,
            last_simplify: 0,
            lazy_remove: Default::default(),
            last_num_lemma: 1000,
        }
    }
}

impl Solver {
    pub fn simplify(&mut self) {
        assert!(self.highest_level() == 0);
        assert!(self.propagate() == CREF_NONE);
        if self.statistic.num_solve > self.simplify.last_simplify + 1000 {
            if self.simplify.last_num_assign < self.trail.len() {
                self.simplify_satisfied();
                self.simplify.last_simplify = self.statistic.num_solve;
            }
            if self.simplify.last_num_lemma + 1000 < self.cdb.lemmas.len() {
                self.simplify_satisfied();
                let lemmas = take(&mut self.cdb.lemmas);
                self.cdb.lemmas = self.simplify_subsume(lemmas);
                self.simplify.last_num_lemma = self.cdb.lemmas.len();
            }
            self.garbage_collect();
        }
    }

    pub fn simplify_satisfied_clauses(&mut self, mut clauses: Gvec<CRef>) -> Gvec<CRef> {
        let mut i = 0;
        while i < clauses.len() {
            let cid = clauses[i];
            if self.clause_satisfied(cid) {
                clauses.swap_remove(i);
                self.detach_clause(cid);
                continue;
            }
            let mut j = 2;
            let mut cls = self.cdb.get(cid);
            while j < cls.len() {
                if self.value.v(cls[j]).is_false() {
                    cls.swap_remove(j);
                    continue;
                }
                j += 1;
            }
            i += 1;
        }
        clauses
    }

    pub fn simplify_satisfied(&mut self) {
        assert!(self.highest_level() == 0);
        if self.simplify.last_num_assign >= self.trail.len() {
            return;
        }
        let lemmas = take(&mut self.cdb.lemmas);
        self.cdb.lemmas = self.simplify_satisfied_clauses(lemmas);
        let learnt = take(&mut self.cdb.learnt);
        self.cdb.learnt = self.simplify_satisfied_clauses(learnt);
        let trans = take(&mut self.cdb.trans);
        self.cdb.trans = self.simplify_satisfied_clauses(trans);
        self.simplify.last_num_assign = self.trail.len();
    }

    fn simplify_subsume(&mut self, clauses: Gvec<CRef>) -> Gvec<CRef> {
        let mut clauses: Vec<(CRef, Lemma)> = clauses
            .into_iter()
            .map(|cref| {
                let cls = self.cdb.get(cref);
                let lemma = Lemma::new(LitVec::from(cls.slice()));
                (cref, lemma)
            })
            .collect();
        clauses.sort_by_key(|(_, l)| l.len());
        let mut occurs: LitMap<Vec<usize>> = LitMap::new_with(self.ts.max_var);
        for (i, cls) in clauses.iter().enumerate() {
            for l in cls.1.iter() {
                occurs[*l].push(i);
            }
        }
        for cls_idx in 0..clauses.len() {
            let cls = self.cdb.get(clauses[cls_idx].0);
            if cls.is_removed() {
                continue;
            }
            let max_occurs = *clauses[cls_idx]
                .1
                .iter()
                .min_by_key(|l| occurs[**l].len())
                .unwrap();
            for subsumed in occurs[max_occurs].iter() {
                let lemma = &clauses[cls_idx].1;
                if *subsumed == cls_idx {
                    continue;
                }
                if self.cdb.get(clauses[*subsumed].0).is_removed() {
                    continue;
                }
                let (res, diff) = lemma.subsume_execpt_one(&clauses[*subsumed].1);
                if res {
                    self.detach_clause(clauses[*subsumed].0);
                    self.statistic.num_simplify_subsume += 1;
                } else if let Some(diff) = diff {
                    self.statistic.num_simplify_self_subsume += 1;
                    if lemma.len() == clauses[*subsumed].1.len() {
                        if lemma.len() > 2 {
                            self.detach_clause(clauses[*subsumed].0);
                            self.strengthen_clause(clauses[cls_idx].0, diff);
                            let strengthen = self.cdb.get(clauses[cls_idx].0);
                            clauses[cls_idx].1 = Lemma::new(LitVec::from(strengthen.slice()));
                        } else {
                            // println!("{}", lemma);
                            // println!("{}", clauses[*subsumed].1);
                            // println!("{}", diff);
                        }
                    } else {
                        self.strengthen_clause(clauses[*subsumed].0, !diff);
                        let strengthen = self.cdb.get(clauses[*subsumed].0);
                        clauses[*subsumed].1 = Lemma::new(LitVec::from(strengthen.slice()));
                    }
                }
            }
        }
        clauses
            .into_iter()
            .map(|(cref, _)| cref)
            .filter(|cref| !self.cdb.get(*cref).is_removed())
            .collect()
    }
}
