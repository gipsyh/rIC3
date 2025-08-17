use super::{
    DagCnfSolver,
    cdb::{CREF_NONE, CRef},
};
use giputils::gvec::Gvec;
use log::debug;
use logicrs::{Lbool, LitOrdVec, LitVec, VarMap};
use std::{mem::take, time::Instant};

#[derive(Clone)]
pub struct Simplify {
    pub last_num_assign: usize,
    pub last_simplify: usize,
    pub lazy_remove: Vec<LitVec>,
    pub last_num_lemma: usize,
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

impl DagCnfSolver {
    pub fn simplify(&mut self) {
        assert!(self.highest_level() == 0);
        assert!(self.propagate() == CREF_NONE);
        if self.statistic.num_solve > self.simplify.last_simplify + 100 {
            if self.simplify.last_num_assign < self.trail.len() {
                self.simplify_satisfied();
            }
            if self.simplify.last_num_lemma + 1000 < self.cdb.lemmas.len() {
                let lemmas = take(&mut self.cdb.lemmas);
                self.cdb.lemmas = self.simplify_subsume(lemmas);
                self.simplify.last_num_lemma = self.cdb.lemmas.len();
            }
            self.clean_eq();
            self.garbage_collect();
            self.simplify.last_simplify = self.statistic.num_solve;
        }
    }

    pub fn simplify_satisfied_clauses(&mut self, mut clauses: Gvec<CRef>) -> Gvec<CRef> {
        let mut i = 0;
        'm: while i < clauses.len() {
            let cid = clauses[i];
            let mut cls = self.cdb.get(cid);
            let mut j = 0;
            while j < cls.len() {
                match self.value.v(cls[j]) {
                    Lbool::TRUE => {
                        clauses.swap_remove(i);
                        self.detach_clause(cid);
                        continue 'm;
                    }
                    Lbool::FALSE => {
                        if j <= 1 {
                            debug_assert!(
                                cls.slice().iter().any(|&l| self.value.v(l) == Lbool::TRUE)
                            );
                            clauses.swap_remove(i);
                            self.detach_clause(cid);
                            continue 'm;
                        } else {
                            cls.swap_remove(j);
                        }
                    }
                    _ => {
                        j += 1;
                    }
                }
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
        let start = Instant::now();
        let mut simplified = 0;
        let lemmas = take(&mut self.cdb.lemmas);
        simplified += lemmas.len();
        self.cdb.lemmas = self.simplify_satisfied_clauses(lemmas);
        simplified -= self.cdb.lemmas.len();
        let learnt = take(&mut self.cdb.learnt);
        simplified += learnt.len();
        self.cdb.learnt = self.simplify_satisfied_clauses(learnt);
        simplified -= self.cdb.learnt.len();
        let trans = take(&mut self.cdb.trans);
        simplified += trans.len();
        self.cdb.trans = self.simplify_satisfied_clauses(trans);
        simplified -= self.cdb.trans.len();
        self.simplify.last_num_assign = self.trail.len();
        debug!(
            "gipsat simplifies {simplified} statisfied clauses in {:?}",
            start.elapsed()
        );
    }

    fn simplify_subsume(&mut self, clauses: Gvec<CRef>) -> Gvec<CRef> {
        debug!("simplify subsume");
        let mut clauses: Vec<(CRef, LitOrdVec)> = clauses
            .into_iter()
            .filter_map(|cref| {
                let cls = self.cdb.get(cref);
                if cls.len() > 100 {
                    None
                } else {
                    let lemma = LitOrdVec::new(LitVec::from(cls.slice()));
                    Some((cref, lemma))
                }
            })
            .collect();
        clauses.sort_by_key(|(_, l)| l.len());
        let mut occurs: VarMap<Vec<usize>> = VarMap::new_with(self.dc.max_var());
        for (i, cls) in clauses.iter().enumerate() {
            for l in cls.1.iter() {
                occurs[l.var()].push(i);
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
                            clauses[cls_idx].1 = LitOrdVec::new(LitVec::from(strengthen.slice()));
                        } else {
                            // println!("{}", lemma);
                            // println!("{}", clauses[*subsumed].1);
                            // println!("{}", diff);
                        }
                    } else {
                        self.strengthen_clause(clauses[*subsumed].0, !diff);
                        let strengthen = self.cdb.get(clauses[*subsumed].0);
                        clauses[*subsumed].1 = LitOrdVec::new(LitVec::from(strengthen.slice()));
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
