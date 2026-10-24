pub mod simplify;
pub mod simulate;
mod top;

use crate::{Cnf, Lit, LitFixedVec, LitVvec, Var, VarLMap, VarMap, VarRange, VarVMap};
use giputils::hash::GHashSet;
use serde::{Deserialize, Serialize};
use std::{
    fmt::Display,
    iter::{Flatten, Zip, once},
    mem::take,
    ops::Index,
    slice,
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DagCnf {
    max_var: Var,
    cnf: VarMap<Vec<LitFixedVec>>,
    dep: VarMap<Box<[Var]>>,
}

impl DagCnf {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.max_var += 1;
        self.dep.reserve(self.max_var);
        self.cnf.reserve(self.max_var);
        self.max_var
    }

    #[inline]
    pub fn new_var_to(&mut self, n: Var) {
        if self.max_var < n {
            self.max_var = n;
            self.dep.reserve(n);
            self.cnf.reserve(n);
        }
    }

    #[inline]
    pub fn max_var(&self) -> Var {
        self.max_var
    }

    #[inline]
    pub fn num_var(&self) -> usize {
        let n: usize = self.max_var().into();
        n + 1
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.clause().count()
    }

    #[inline]
    pub fn var_iter(&self) -> VarRange {
        VarRange::new_inclusive(Var::CONST, self.max_var)
    }

    /// var iter wo const
    #[inline]
    pub fn var_iter_woc(&self) -> VarRange {
        VarRange::new_inclusive(Var(1), self.max_var)
    }

    #[inline]
    pub fn num_clause(&self) -> usize {
        self.cnf.iter().map(|v| v.len()).sum()
    }

    /// Estimate the heap memory (in bytes) held by this `DagCnf`, based on the
    /// allocated capacities of the underlying vectors. This covers `cnf` (the
    /// per-variable clause lists) and `dep` (the per-variable dependency lists);
    /// the stack footprint of the struct itself is not included. Literal
    /// buffers shortened in place may retain additional uncounted space.
    pub fn mem_usage(&self) -> usize {
        let mut bytes = 0usize;
        bytes += self.cnf.capacity() * std::mem::size_of::<Vec<LitFixedVec>>();
        for lv in self.cnf.iter() {
            bytes += lv.capacity() * std::mem::size_of::<LitFixedVec>();
            for cls in lv.iter() {
                bytes += cls.mem_usage();
            }
        }
        bytes += self.dep.capacity() * std::mem::size_of::<Box<[Var]>>();
        for d in self.dep.iter() {
            bytes += d.len() * std::mem::size_of::<Var>();
        }
        bytes
    }

    #[inline]
    pub fn clause(&self) -> Flatten<slice::Iter<'_, Vec<LitFixedVec>>> {
        self.cnf.iter().flatten()
    }

    /// Discard dependency information and move the clauses into a flat CNF.
    /// Unlike `lower`, this consumes the DAG without cloning literal buffers.
    pub fn into_cnf(mut self) -> Cnf {
        drop(take(&mut self.dep));
        let mut clauses = Vec::with_capacity(self.num_clause());
        for rel in self.cnf.iter_mut() {
            clauses.extend(take(rel));
        }
        let mut result = Cnf::new();
        result.new_var_to(self.max_var);
        result.set_cls(clauses);
        result
    }

    #[inline]
    pub fn dep(&self, n: Var) -> &[Var] {
        &self.dep[n]
    }

    pub fn refs(&self) -> VarMap<Vec<Var>> {
        let mut refs: VarMap<Vec<Var>> = VarMap::new_with(self.max_var);
        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            for &dep in self.dep[v].iter() {
                refs[dep].push(v);
            }
        }
        refs
    }

    #[inline]
    pub fn iter(&self) -> Zip<VarRange, std::slice::Iter<'_, Vec<LitFixedVec>>> {
        VarRange::new_inclusive(Var::CONST, self.max_var).zip(self.cnf.iter())
    }

    #[inline]
    pub fn add_rel(&mut self, n: Var, rel: &[impl AsRef<[Lit]>]) {
        self.add_rel_owned(n, rel.iter().map(|r| LitFixedVec::from(r.as_ref())));
    }

    #[inline]
    pub fn add_rel_owned(&mut self, n: Var, rel: impl IntoIterator<Item = impl Into<LitFixedVec>>) {
        self.new_var_to(n);
        let source = rel.into_iter();
        // Do not reuse a Vec<LitVec> allocation through in-place collection:
        // its 24-byte slots would retain the memory saved by 8-byte handles.
        let mut rel = Vec::<LitFixedVec>::with_capacity(source.size_hint().0);
        for cls in source {
            rel.push(cls.into());
        }
        if n.is_constant() {
            assert!(rel.len() == 1 && rel[0].as_slice() == [Lit::TRUE]);
            return;
        }
        assert!(self.dep[n].is_empty() && self.cnf[n].is_empty());
        for r in &mut rel {
            r.sort();
            assert!(r.last().var() == n);
        }
        self.dep[n] = deps(n, &rel);
        self.cnf[n] = rel;
    }

    #[inline]
    pub fn set_rel(&mut self, n: Var, rel: &[impl AsRef<[Lit]>]) {
        self.new_var_to(n);
        self.dep[n] = Box::default();
        self.cnf[n].clear();
        self.add_rel(n, rel);
    }

    #[inline]
    pub fn del_rel(&mut self, n: Var) {
        self.dep[n] = Box::default();
        self.cnf[n].clear();
    }

    #[inline]
    pub fn has_rel(&self, n: Var) -> bool {
        n.is_constant() || !self.cnf[n].is_empty()
    }

    #[inline]
    pub fn is_leaf(&self, n: Var) -> bool {
        self.cnf[n].is_empty()
    }

    #[inline]
    pub fn new_and(&mut self, ands: impl IntoIterator<Item = impl Into<Lit>>) -> Lit {
        let mut and = Vec::new();
        for a in ands.into_iter() {
            let a = a.into();
            if a.is_constant(true) {
                continue;
            }
            if a.is_constant(false) {
                return Lit::FALSE;
            }
            and.push(a);
        }
        if and.is_empty() {
            Lit::TRUE
        } else if and.len() == 1 {
            and[0]
        } else {
            let n = self.new_var().lit();
            self.add_rel(n.var(), &LitVvec::cnf_and(n, &and));
            n
        }
    }

    #[inline]
    pub fn new_or(&mut self, ors: impl IntoIterator<Item = impl Into<Lit>>) -> Lit {
        let mut or = Vec::new();
        for o in ors.into_iter() {
            let o = o.into();
            if o.is_constant(false) {
                continue;
            }
            if o.is_constant(true) {
                return Lit::TRUE;
            }
            or.push(o);
        }
        if or.is_empty() {
            Lit::FALSE
        } else if or.len() == 1 {
            or[0]
        } else {
            let n = self.new_var().lit();
            self.add_rel(n.var(), &LitVvec::cnf_or(n, &or));
            n
        }
    }

    #[inline]
    pub fn new_xor(&mut self, mut x: Lit, mut y: Lit) -> Lit {
        if x.var() == y.var() {
            return Lit::constant(x != y);
        }
        if x.var() > y.var() {
            (x, y) = (y, x);
        }
        if x.is_constant(true) {
            return !y;
        } else if x.is_constant(false) {
            return y;
        }
        let n = self.new_var().lit();
        self.add_rel(n.var(), &LitVvec::cnf_xor(n, x, y));
        n
    }

    #[inline]
    pub fn new_xnor(&mut self, mut x: Lit, mut y: Lit) -> Lit {
        if x.var() == y.var() {
            return Lit::constant(x == y);
        }
        if x.var() > y.var() {
            (x, y) = (y, x);
        }
        if x.is_constant(true) {
            return y;
        } else if x.is_constant(false) {
            return !y;
        }
        let n = self.new_var().lit();
        self.add_rel(n.var(), &LitVvec::cnf_xnor(n, x, y));
        n
    }

    #[inline]
    pub fn new_imply(&mut self, x: Lit, y: Lit) -> Lit {
        let n = self.new_var().lit();
        self.add_rel(n.var(), &LitVvec::cnf_or(n, &[!x, y]));
        n
    }

    #[inline]
    pub fn new_ite(&mut self, c: Lit, t: Lit, e: Lit) -> Lit {
        let n = self.new_var().lit();
        self.add_rel(n.var(), &LitVvec::cnf_ite(n, c, t, e));
        n
    }

    pub fn fanins(&self, var: impl IntoIterator<Item = impl Into<Var>>) -> GHashSet<Var> {
        let mut marked = GHashSet::new();
        let mut queue = vec![];
        for v in var.into_iter().map(|v| v.into()) {
            marked.insert(v);
            queue.push(v);
        }
        while let Some(v) = queue.pop() {
            for d in self.dep[v].iter() {
                if !marked.contains(d) {
                    marked.insert(*d);
                    queue.push(*d);
                }
            }
        }
        marked
    }

    pub fn fanouts(&self, var: impl IntoIterator<Item = impl Into<Var>>) -> GHashSet<Var> {
        let mut marked = GHashSet::from_iter(var.into_iter().map(|v| v.into()));
        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            if self.dep[v].iter().any(|d| marked.contains(d)) {
                marked.insert(v);
            }
        }
        marked
    }

    pub fn root(&self) -> GHashSet<Var> {
        let mut root = GHashSet::from_iter(
            VarRange::new_inclusive(Var::CONST, self.max_var())
                .filter(|v| !self.dep[*v].is_empty()),
        );
        for d in self.dep.iter() {
            for d in d.iter() {
                root.remove(d);
            }
        }
        root
    }

    pub fn pol_filter(&mut self, pol: impl IntoIterator<Item = impl Into<Lit>>) {
        for p in pol.into_iter().map(|l| l.into()) {
            self.cnf[p.var()].retain(|cls| cls.last() != !p);
            self.dep[p.var()] = deps(p.var(), &self.cnf[p.var()]);
        }
    }

    pub fn rearrange(&mut self, additional: impl IntoIterator<Item = impl Into<Var>>) -> VarVMap {
        let mut domain = GHashSet::from_iter(
            additional
                .into_iter()
                .map(|l| l.into())
                .chain(once(Var::CONST)),
        );
        for cls in self.clause() {
            for l in cls.iter() {
                domain.insert(l.var());
            }
        }
        let mut domain = Vec::from_iter(domain);
        domain.sort();
        let mut domain_map = VarVMap::new();
        let mut res = DagCnf::new();
        for (i, d) in domain.iter().enumerate() {
            let v = Var::new(i);
            res.new_var_to(v);
            domain_map.insert(*d, v);
        }
        let map_lit = |l: &Lit| l.map_var(|v| domain_map[v]);
        for (i, d) in domain.iter().enumerate() {
            if d.is_constant() {
                continue;
            }
            let mut cls = take(&mut self.cnf[*d]);
            for r in cls.iter_mut() {
                for l in r.iter_mut() {
                    *l = map_lit(l);
                }
            }
            res.add_rel_owned(Var::new(i), cls);
        }
        *self = res;
        domain_map
    }

    pub fn map(&self, map: impl Fn(Var) -> Var) -> Self {
        assert!(map(Var::CONST) == Var::CONST);
        let mut res = DagCnf::new();
        for (v, rel) in self.iter() {
            let new_cls: Vec<_> = rel.iter().map(|cls| cls.map(|l| l.map_var(&map))).collect();
            res.add_rel(map(v), &new_cls);
        }
        res
    }

    pub fn replace(&mut self, map: &VarLMap) {
        for (old, new) in map.iter() {
            assert!(*old > new.var());
        }

        for v in VarRange::new_inclusive(Var::CONST, self.max_var) {
            if map.contains_key(&v) {
                self.cnf[v].clear();
                self.dep[v] = Box::default();
            }
            for cls in self.cnf[v].iter_mut() {
                for l in cls.iter_mut() {
                    if let Some(new) = map.map_lit(*l) {
                        *l = new;
                    }
                }
            }
            for d in self.dep[v].iter_mut() {
                if let Some(new) = map.map(*d) {
                    *d = new.var();
                }
            }
        }
    }

    pub fn migrate(&mut self, other: &DagCnf, t: Var, map: &mut VarVMap) {
        if map.get(&t).is_some() {
            return;
        }
        for rel in other[t].iter() {
            for &l in rel.iter() {
                if l.var() != t {
                    self.migrate(other, l.var(), map);
                }
            }
        }
        let n = self.new_var();
        map.insert(t, n);
        let mut new_rel = Vec::new();
        for rel in other[t].iter() {
            new_rel.push(rel.map(|l| map.lit_map(l).unwrap()));
        }
        self.add_rel(n, &new_rel);
    }
}

impl Default for DagCnf {
    fn default() -> Self {
        let max_var = Var::CONST;
        let mut cnf: VarMap<Vec<LitFixedVec>> = VarMap::new_with(max_var);
        cnf[max_var].push(LitFixedVec::from([Lit::TRUE]));
        Self {
            max_var,
            cnf,
            dep: VarMap::new_with(max_var),
        }
    }
}

impl Index<Var> for DagCnf {
    type Output = [LitFixedVec];

    #[inline]
    fn index(&self, index: Var) -> &Self::Output {
        &self.cnf[index]
    }
}

impl Display for DagCnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for cls in self.clause() {
            writeln!(f, "{cls}")?;
        }
        Ok(())
    }
}

#[inline]
fn deps(n: Var, cnf: &[LitFixedVec]) -> Box<[Var]> {
    if cnf.len() > 16 || cnf.iter().any(|cls| cls.len() > 16) {
        let mut dep = GHashSet::new();
        for cls in cnf {
            for l in cls {
                if l.var() != n {
                    dep.insert(l.var());
                }
            }
        }
        return dep.into_iter().collect::<Vec<_>>().into_boxed_slice();
    }
    let mut dep = Vec::new();
    for cls in cnf.iter() {
        for l in cls.iter() {
            let v = l.var();
            if v != n && !dep.contains(&v) {
                dep.push(v);
            }
        }
    }
    dep.into_boxed_slice()
}
