use super::DagCnf;
use crate::{
    LitFixedVec, LitMap, LitOrdVec, LitVvec, Var, VarAssign, VarRange, lemmas_subsume_simplify,
    occur::Occurs,
};
use giputils::{allocator::Gallocator, hash::GHashSet, ptr::Grc};
use log::debug;
use std::{
    iter::once,
    time::{Duration, Instant},
};

/// Cost bounded by each variable elimination, before resolvent subsumption.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BveObjective {
    #[default]
    Clauses,
    Literals,
}

pub struct DagCnfSimplify {
    cdb: Grc<Gallocator<LitFixedVec>>,
    max_var: Var,
    cnf: LitMap<Vec<usize>>,
    occur: Option<Occurs<LitFixedVec>>,
    frozen: GHashSet<Var>,
    value: VarAssign,
    num_ocls: usize,
    time: Duration,
}

impl DagCnfSimplify {
    pub fn new(dagcnf: &DagCnf) -> Self {
        Self::from_rels(
            dagcnf.max_var,
            dagcnf.num_clause(),
            dagcnf.cnf.iter().cloned(),
        )
    }

    /// Consume clauses one relation at a time and release dependency lists
    /// before allocating the simplifier's occurrence lists.
    pub fn from_owned(mut dagcnf: DagCnf) -> Self {
        let num_ocls = dagcnf.num_clause();
        drop(std::mem::take(&mut dagcnf.dep));
        Self::from_rels(
            dagcnf.max_var,
            num_ocls,
            dagcnf.cnf.iter_mut().map(std::mem::take),
        )
    }

    fn from_rels(
        max_var: Var,
        num_ocls: usize,
        rels: impl IntoIterator<Item = Vec<LitFixedVec>>,
    ) -> Self {
        let cdb = Grc::new(Gallocator::new());
        let cnf = LitMap::new_with(max_var);
        let value = VarAssign::new_with(max_var);
        let mut res = Self {
            cdb,
            occur: None,
            max_var,
            cnf,
            frozen: GHashSet::from_iter([Var::CONST]),
            value,
            num_ocls,
            time: Duration::default(),
        };
        for (v, rel) in VarRange::new_inclusive(Var::CONST, max_var).zip(rels) {
            for mut cls in rel {
                cls.sort();
                cls.dedup();
                assert!(cls.last().var().eq(&v));
                res.add_rel(cls);
            }
        }
        res
    }

    fn enable_occur(&mut self) {
        if self.occur.is_none() {
            let mut occur = Occurs::new_with(self.max_var, self.cdb.clone());
            for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
                for &cls in self.cnf[v.lit()].iter().chain(self.cnf[!v.lit()].iter()) {
                    for &l in self.cdb[cls].iter() {
                        let lv = l.var();
                        if lv != v {
                            occur.add(l, cls);
                        }
                    }
                }
            }
            self.occur = Some(occur);
        }
    }

    fn disable_occur(&mut self) {
        if self.occur.is_some() {
            self.occur = None;
        }
    }

    pub fn froze(&mut self, v: Var) {
        self.frozen.insert(v);
    }

    fn add_rel(&mut self, rel: LitFixedVec) {
        let Some(rel) = rel.ordered_simp(&self.value) else {
            return;
        };
        let n = rel.last();
        if rel.len() == 1 {
            assert!(!self.value.v(n).is_true());
            self.value.set(n);
        }
        let relid = self.cdb.alloc(rel);
        self.cnf[n].push(relid);
        if let Some(occur) = &mut self.occur {
            for &l in self.cdb[relid].iter() {
                let lv = l.var();
                if lv != n.var() {
                    occur.add(l, relid);
                }
            }
        }
    }

    fn dealloc_rel(&mut self, cls: usize) {
        self.cdb.dealloc(cls);
        self.cdb[cls] = LitFixedVec::new();
    }

    #[allow(unused)]
    fn remove_rel(&mut self, rel: usize) {
        let o = self.cdb[rel].last();
        let mut i = 0;
        while i < self.cnf[o].len() {
            if self.cnf[o][i] == rel {
                let cls = self.cnf[o].swap_remove(i);
                if let Some(occur) = &mut self.occur {
                    for &l in self.cdb[cls].iter() {
                        let lv = l.var();
                        if lv != o.var() {
                            occur.del(l, cls);
                        }
                    }
                }
                self.dealloc_rel(cls);
            } else {
                i += 1;
            }
        }
    }

    fn remove_rels(&mut self, rels: Vec<usize>) {
        let mut outs = Vec::with_capacity(rels.len());
        for cls in rels {
            let o = self.cdb[cls].last();
            outs.push(o);
            if let Some(occur) = &mut self.occur {
                for &l in self.cdb[cls].iter() {
                    if l.var() != o.var() {
                        occur.del(l, cls);
                    }
                }
            }
            self.dealloc_rel(cls);
        }
        // Use the allocator tombstones to filter each affected relation once.
        outs.sort_unstable();
        outs.dedup();
        for o in outs {
            self.cnf[o].retain(|&cls| !self.cdb.is_removed(cls));
        }
    }

    #[inline]
    fn remove_node(&mut self, n: Var) {
        let ln = n.lit();
        if let Some(occur) = &mut self.occur {
            assert!(occur.num_occur(ln) == 0 && occur.num_occur(!ln) == 0);
        }
        for &cls in self.cnf[ln].iter().chain(self.cnf[!ln].iter()) {
            if let Some(occur) = &mut self.occur {
                for &l in self.cdb[cls].iter() {
                    let lv = l.var();
                    if lv != n {
                        occur.del(l, cls);
                    }
                }
            }
            self.cdb.dealloc(cls);
            self.cdb[cls] = LitFixedVec::new();
        }
        self.cnf[ln] = Vec::new();
        self.cnf[!ln] = Vec::new();
    }

    fn var_rels(&self, v: Var) -> Vec<usize> {
        self.cnf[v.lit()]
            .iter()
            .chain(self.cnf[!v.lit()].iter())
            .copied()
            .collect()
    }

    fn resolvent(
        &self,
        pcnf: &[usize],
        ncnf: &[usize],
        pivot: Var,
        budget: &mut usize,
        objective: BveObjective,
    ) -> Option<LitVvec> {
        let mut res = LitVvec::new();
        for &pcls in pcnf {
            for &ncls in ncnf {
                if let Some(resolvent) = self.cdb[pcls].ordered_resolvent(&self.cdb[ncls], pivot) {
                    let cost = match objective {
                        BveObjective::Clauses => 1,
                        BveObjective::Literals => resolvent.len(),
                    };
                    *budget = budget.checked_sub(cost)?;
                    res.push(resolvent);
                }
            }
        }
        Some(res)
    }

    fn eliminate(&mut self, v: Var, objective: BveObjective) {
        if self.frozen.contains(&v) {
            return;
        }
        let lv = v.lit();
        let occur = self.occur.as_mut().unwrap();
        let ocost =
            occur.num_occur(lv) + occur.num_occur(!lv) + self.cnf[lv].len() + self.cnf[!lv].len();
        if ocost == 0 || ocost > 2000 {
            return;
        }
        let (pos, neg) = (&self.cnf[lv], &self.cnf[!lv]);
        let mut opos = occur.get(lv).to_vec();
        let oneg = occur.get(!lv).to_vec();
        // Share one budget across both polarities and reject growth before
        // subsumption. Clause mode retains the original acceptance criterion;
        // literal mode also accounts for the lengths of the resolvents.
        let mut budget = match objective {
            BveObjective::Clauses => ocost,
            BveObjective::Literals => pos
                .iter()
                .chain(neg)
                .chain(&opos)
                .chain(&oneg)
                .map(|&c| self.cdb[c].len() as usize)
                .sum(),
        };
        let Some(respn) = self.resolvent(pos, &oneg, v, &mut budget, objective) else {
            return;
        };
        let Some(resnp) = self.resolvent(neg, &opos, v, &mut budget, objective) else {
            return;
        };
        let mut res = respn;
        res.extend(resnp);
        let res = clause_subsume_simplify(res);
        opos.extend(oneg);
        self.remove_rels(opos);
        self.remove_node(v);
        for r in res {
            self.add_rel(r.into());
        }
    }

    pub fn bve_simplify(&mut self) {
        self.bve_simplify_with_objective(BveObjective::default());
    }

    pub fn bve_simplify_with_objective(&mut self, objective: BveObjective) {
        let start = Instant::now();
        self.enable_occur();
        // Relations are topologically ordered. Visit each variable once, so
        // accepted substitutions reach later gates without maintaining a heap.
        for v in VarRange::new_inclusive(Var(1), self.max_var) {
            self.eliminate(v, objective);
        }
        debug!("bve ({objective:?}) completed in {:?}", start.elapsed());
        self.time += start.elapsed();
    }

    fn cls_subsume_check(&mut self, ci: usize) {
        if self.cdb.is_removed(ci) {
            return;
        }
        let occur = self.occur.as_mut().unwrap();
        let best_lit = *self.cdb[ci]
            .iter()
            .min_by_key(|&&l| {
                occur.num_occur(l) + occur.num_occur(!l) + self.cnf[l].len() + self.cnf[!l].len()
            })
            .unwrap();
        let mut occurs = occur.get(best_lit).to_vec();
        occurs.extend_from_slice(occur.get(!best_lit));
        occurs.extend(self.cnf[best_lit].iter());
        occurs.extend(self.cnf[!best_lit].iter());
        for cj in occurs {
            if self.cdb.is_removed(cj) {
                continue;
            }
            if cj == ci {
                continue;
            }
            let (res, diff) = self.cdb[ci].ordered_subsume_execpt_one(&self.cdb[cj]);
            if res {
                self.cnf[self.cdb[cj].last()].retain(|&c| c != cj);
                self.dealloc_rel(cj);
                continue;
            } else if let Some(diff) = diff {
                if self.cdb[ci].len() == self.cdb[cj].len() {
                    if diff.var() == self.cdb[ci].last().var() {
                        self.cnf[self.cdb[ci].last()].retain(|&c| c != ci);
                        self.cnf[self.cdb[cj].last()].retain(|&c| c != cj);
                        self.dealloc_rel(ci);
                        self.dealloc_rel(cj);
                        return;
                    }
                    self.cdb[ci].retain(|l| *l != diff);
                    self.cnf[self.cdb[cj].last()].retain(|&c| c != cj);
                    self.dealloc_rel(cj);
                } else if diff.var() == self.cdb[cj].last().var() {
                    self.cnf[self.cdb[cj].last()].retain(|&c| c != cj);
                    self.dealloc_rel(cj);
                } else {
                    self.cdb[cj].retain(|l| *l != !diff);
                }
            }
        }
    }

    pub fn subsume_simplify(&mut self) {
        let start = Instant::now();
        self.enable_occur();
        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            for cls in self.cnf[v.lit()].clone() {
                self.cls_subsume_check(cls);
            }
            for cls in self.cnf[!v.lit()].clone() {
                self.cls_subsume_check(cls);
            }
        }
        self.disable_occur();
        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            self.cnf[v.lit()].retain(|&c| !self.cdb.is_removed(c));
            self.cnf[!v.lit()].retain(|&c| !self.cdb.is_removed(c));
        }
        self.time += start.elapsed();
    }

    fn const_simp_var(&mut self, v: Var) {
        let cls = self.var_rels(v);
        let mut removed = Vec::new();
        for c in cls {
            let cls = self.cdb[c].clone();
            let len = cls.len();
            if let Some(scls) = cls.ordered_simp(&self.value) {
                if scls.last().var() != v {
                    removed.push(c);
                } else if len != scls.len() {
                    self.add_rel(scls);
                }
            } else {
                removed.push(c);
            }
        }
        self.remove_rels(removed);
    }

    pub fn const_simplify(&mut self) {
        let start = Instant::now();
        self.disable_occur();
        for v in VarRange::new_inclusive(Var(1), self.max_var) {
            self.const_simp_var(v);
        }
        for v in VarRange::new_inclusive(Var(1), self.max_var) {
            let ln = v.lit();
            let vv = self.value.v(ln);
            if !vv.is_none() {
                self.remove_node(v);
                if self.frozen.contains(&v) {
                    self.add_rel(LitFixedVec::from([ln.not_if(vv.is_false())]));
                }
            }
        }
        self.time += start.elapsed();
    }

    pub fn finalize(&mut self) -> DagCnf {
        self.finalize_impl(false)
    }

    fn finalize_impl(&mut self, consume: bool) -> DagCnf {
        let start = Instant::now();
        let mut dagcnf = DagCnf::new();
        dagcnf.new_var_to(self.max_var);
        for v in VarRange::new_inclusive(Var(1), self.max_var) {
            let mut cnf: Vec<LitFixedVec> = self.cnf[v.lit()]
                .iter()
                .chain(self.cnf[!v.lit()].iter())
                .map(|&cls| {
                    assert!(!self.cdb.is_removed(cls));
                    if consume {
                        std::mem::take(&mut self.cdb[cls])
                    } else {
                        self.cdb[cls].clone()
                    }
                })
                .collect();
            if self.frozen.contains(&v)
                && let Some(vl) = self.value.vl(v)
            {
                cnf.clear();
                cnf.push(LitFixedVec::from([vl]));
            }
            dagcnf.add_rel_owned(v, cnf);
            if consume {
                self.cnf[v.lit()] = Vec::new();
                self.cnf[!v.lit()] = Vec::new();
            }
        }
        self.time += start.elapsed();
        debug!(
            "dagcnf simplified from {} to {} clauses in {:.2}s",
            self.num_ocls,
            dagcnf.num_clause(),
            self.time.as_secs_f64()
        );
        dagcnf
    }

    pub fn simplify(&mut self) -> DagCnf {
        self.simplify_with_objective(BveObjective::default())
    }

    pub fn simplify_with_objective(&mut self, objective: BveObjective) -> DagCnf {
        self.const_simplify();
        self.bve_simplify_with_objective(objective);
        self.subsume_simplify();
        self.finalize()
    }
}

fn clause_subsume_simplify(lemmas: LitVvec) -> LitVvec {
    let lemmas: Vec<LitOrdVec> = lemmas.into_iter().map(LitOrdVec::new).collect();
    let lemmas = lemmas_subsume_simplify(lemmas);
    lemmas.into_iter().map(LitOrdVec::into_litvec).collect()
}

impl DagCnf {
    pub fn simplify(self, frozen: impl IntoIterator<Item = impl Into<Var>>) -> Self {
        self.simplify_with_objective(frozen, BveObjective::default())
    }

    pub fn simplify_with_objective(
        self,
        frozen: impl IntoIterator<Item = impl Into<Var>>,
        objective: BveObjective,
    ) -> Self {
        let mut simp = DagCnfSimplify::from_owned(self);
        for v in frozen.into_iter().map(|l| l.into()).chain(once(Var::CONST)) {
            simp.froze(v);
        }
        simp.const_simplify();
        simp.bve_simplify_with_objective(objective);
        simp.subsume_simplify();
        simp.finalize_impl(true)
    }
}

#[cfg(test)]
mod test {
    use crate::{DagCnf, Lit, Var, VarRange, simplify::DagCnfSimplify};

    #[test]
    fn test0() {
        let mut dc = DagCnf::new();
        dc.new_var_to(Var(4));
        dc.new_and([Lit::from(1), Lit::from(2), Lit::from(3)]);
        dc.new_and([Lit::from(1), Lit::from(2), Lit::from(3), Lit::from(4)]);
        println!("{dc}");
        let mut simp = DagCnfSimplify::new(&dc);
        for v in VarRange::new_inclusive(Var::CONST, dc.max_var()) {
            simp.froze(v);
        }
        let ndc = simp.simplify();
        println!("{ndc}");
    }
}
