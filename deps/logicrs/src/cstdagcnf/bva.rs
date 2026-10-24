use crate::{Cnf, CstDagCnf, DagCnf, Lit, LitMap, LitOrdVec, LitVec, Var, VarRange, occur::Occurs};
use giputils::{allocator::Gallocator, ptr::Grc};
use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashMap, HashSet},
};

pub struct BVA {
    cdb: Grc<Gallocator<LitOrdVec>>,
    occur: Occurs<LitOrdVec>,
    dc: DagCnf,
    lit_count_adjust: LitMap<usize>,
}

impl BVA {
    pub fn new(cnf: Cnf) -> Self {
        let cdb = Grc::new(Gallocator::new());
        let occur = Occurs::new(cdb.clone());
        let mut lit_count_adjust: LitMap<usize> = LitMap::new();
        let mut dc = DagCnf::new();
        dc.new_var_to(cnf.max_var());
        lit_count_adjust.reserve(cnf.max_var());
        let mut res = Self {
            cdb,
            occur,
            dc,
            lit_count_adjust,
        };
        for cls in cnf.clauses() {
            res.add_clause(cls);
        }
        res
    }

    fn reserve(&mut self, var: Var) {
        assert!(self.dc.max_var() >= var);
        self.occur.reserve(var);
        self.lit_count_adjust.reserve(var);
    }

    fn add_clause(&mut self, rel: &[Lit]) {
        let rel = LitOrdVec::from(rel);
        let relid = self.cdb.alloc(rel);
        for l in self.cdb[relid].clone() {
            self.reserve(l.var());
            self.occur.add(l, relid);
        }
    }

    fn del_clause(&mut self, cls: usize) {
        for &l in self.cdb[cls].iter() {
            self.occur.del(l, cls);
        }
        self.cdb.dealloc(cls);
    }

    #[inline]
    fn lit_count(&self, lit: Lit) -> isize {
        self.occur.num_occur(lit) as isize - self.lit_count_adjust[lit] as isize
    }

    fn least_frequent_not(&self, cls: usize, lit: Lit) -> Option<Lit> {
        self.cdb[cls]
            .iter()
            .filter(|l| **l != lit)
            .min_by_key(|l| self.lit_count(**l))
            .cloned()
    }

    pub fn bva(mut self) -> CstDagCnf {
        let mut queue = BinaryHeap::new();
        for v in VarRange::new_inclusive(Var::CONST, self.dc.max_var()) {
            let l = v.lit();
            queue.push(QueueElement(l, self.lit_count(l)));
            queue.push(QueueElement(!l, self.lit_count(!l)));
        }
        while let Some(QueueElement(max_lit, num_cls)) = queue.pop() {
            if num_cls == 0 || num_cls != self.lit_count(max_lit) {
                continue;
            }
            let mut matched_clauses: Vec<Vec<usize>> = self
                .occur
                .get(max_lit)
                .iter()
                .map(|cls| vec![*cls])
                .collect();
            let mut matched_lits = vec![max_lit];
            loop {
                let mut matched_entries: HashMap<Lit, Vec<(usize, usize)>> = HashMap::new();
                for (mcls_idx, mclss) in matched_clauses.iter().enumerate() {
                    let mcls = mclss[0];
                    let Some(least) = self.least_frequent_not(mcls, max_lit) else {
                        continue;
                    };
                    for &ocls in self.occur.get(least).iter() {
                        if self.cdb[mcls].len() != self.cdb[ocls].len() {
                            continue;
                        }
                        let intersection = self.cdb[mcls].ordered_intersection(&self.cdb[ocls]);
                        if intersection.len() + 1 != self.cdb[mcls].len()
                            || intersection.contains(&max_lit)
                        {
                            continue;
                        }
                        let lit = *self.cdb[ocls]
                            .iter()
                            .find(|l| !intersection.contains(l))
                            .unwrap();
                        if !matched_lits.contains(&lit) {
                            let entry = matched_entries.entry(lit).or_default();
                            entry.push((ocls, mcls_idx));
                        }
                    }
                }
                if matched_entries.is_empty() {
                    break;
                }
                let lmax_count = matched_entries.values().map(|v| v.len()).max().unwrap();
                let mut ties: Vec<_> = matched_entries
                    .iter()
                    .filter(|(_, v)| v.len() == lmax_count)
                    .map(|(l, _)| *l)
                    .collect();
                ties.sort();
                let prev_clause_count = matched_clauses.len();
                let new_clause_count = lmax_count;
                let prev_lit_count = matched_lits.len();
                let new_lit_count = prev_lit_count + 1;

                if prev_clause_count * prev_lit_count + new_clause_count + new_lit_count
                    > new_clause_count * new_lit_count + prev_clause_count + prev_lit_count
                {
                    break;
                }
                matched_lits.push(ties[0]);
                for (ocls, mcls_idx) in matched_entries.get(&ties[0]).unwrap().iter() {
                    matched_clauses[*mcls_idx].push(*ocls);
                    assert!(matched_clauses[*mcls_idx].len() == matched_lits.len());
                }
                matched_clauses.retain(|m| m.len() == matched_lits.len());
            }
            if matched_lits.len() * matched_clauses.len()
                <= matched_lits.len() + matched_clauses.len() + 1
            {
                continue;
            }
            let nl = self.dc.new_and(matched_lits);
            for mcls in matched_clauses.iter() {
                let mut cls = LitVec::from([nl]);
                for l in self.cdb[mcls[0]].iter() {
                    if *l != max_lit {
                        cls.push(*l);
                    }
                }
                self.add_clause(&cls);
            }
            let mut lits_to_update = HashSet::new();
            for mcls in matched_clauses.iter() {
                for &cls in mcls.iter() {
                    for &l in self.cdb[cls].iter() {
                        lits_to_update.insert(l);
                        self.lit_count_adjust[l] += 1;
                    }
                    self.del_clause(cls);
                }
            }
            let mut lits_to_update = Vec::from_iter(lits_to_update);
            lits_to_update.sort();
            for lit in lits_to_update {
                queue.push(QueueElement(lit, self.lit_count(lit)));
            }
            queue.push(QueueElement(nl, self.lit_count(nl)));
            queue.push(QueueElement(!nl, self.lit_count(!nl)));
            queue.push(QueueElement(max_lit, self.lit_count(max_lit)));
        }

        let mut cst = Cnf::new();
        for v in VarRange::new_inclusive(Var(1), self.dc.max_var()) {
            let mut cls = self.occur.get(v.lit()).to_vec();
            cls.extend(self.occur.get(!v.lit()).iter().copied());
            cls.into_iter().for_each(|cls| {
                if !self.cdb.is_removed(cls) {
                    cst.add_clause(self.cdb[cls].as_litvec());
                    self.cdb.dealloc(cls);
                }
            });
        }
        CstDagCnf { dag: self.dc, cst }
    }
}

#[derive(PartialEq, Eq)]
struct QueueElement(Lit, isize);

impl PartialOrd for QueueElement {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for QueueElement {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.1.cmp(&other.1) {
            Ordering::Equal => self.0.cmp(&other.0),
            o => o,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Cnf;

    #[test]
    fn test0() {
        let mut cnf = Cnf::new();
        cnf.add_clause(&[Lit::from(1), Lit::from(3)]);
        cnf.add_clause(&[Lit::from(1), Lit::from(4)]);
        cnf.add_clause(&[Lit::from(1), Lit::from(5)]);
        cnf.add_clause(&[Lit::from(1), Lit::from(6)]);
        cnf.add_clause(&[Lit::from(2), Lit::from(3)]);
        cnf.add_clause(&[Lit::from(2), Lit::from(4)]);
        cnf.add_clause(&[Lit::from(2), Lit::from(5)]);
        cnf.add_clause(&[Lit::from(2), Lit::from(6)]);
        let bva = BVA::new(cnf);
        dbg!(bva.bva());
    }

    #[test]
    fn test1() {
        let mut cnf = Cnf::new();
        cnf.add_clause(&[Lit::from(1), Lit::from(-2), Lit::from(3)]);
        cnf.add_clause(&[Lit::from(-1), Lit::from(2), Lit::from(3)]);
        cnf.add_clause(&[Lit::from(1), Lit::from(-2), Lit::from(4)]);
        cnf.add_clause(&[Lit::from(-1), Lit::from(2), Lit::from(4)]);
        cnf.add_clause(&[Lit::from(1), Lit::from(-2), Lit::from(5)]);
        cnf.add_clause(&[Lit::from(-1), Lit::from(2), Lit::from(5)]);
        let bva = BVA::new(cnf);
        dbg!(bva.bva());
    }
}
