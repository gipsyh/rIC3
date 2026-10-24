use crate::{DagCnf, Lit, LitFixedVec, LitVvec, Var, VarVMap};
use giputils::hash::GHashSet;
use std::{
    iter::once,
    ops::{Deref, DerefMut},
};

#[derive(Debug, Clone)]
pub struct Cnf {
    max_var: Var,
    cls: Vec<LitFixedVec>,
}

impl Cnf {
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn max_var(&self) -> Var {
        self.max_var
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.max_var += 1;
        self.max_var
    }

    #[inline]
    pub fn new_var_to(&mut self, n: Var) {
        self.max_var = self.max_var.max(n);
    }

    #[inline]
    pub fn add_clause(&mut self, cls: &[Lit]) {
        if let Some(m) = cls.iter().map(|l| l.var()).max() {
            self.max_var = self.max_var.max(m);
        }
        self.cls.push(LitFixedVec::from(cls));
    }

    #[inline]
    pub fn add_clauses(&mut self, cls: impl IntoIterator<Item = impl AsRef<[Lit]>>) {
        for cls in cls {
            self.add_clause(cls.as_ref());
        }
    }

    #[inline]
    pub fn clauses(&self) -> &[LitFixedVec] {
        &self.cls
    }

    pub fn rearrange(&mut self, additional: impl IntoIterator<Item = impl Into<Var>>) -> VarVMap {
        let mut domain = GHashSet::from_iter(
            additional
                .into_iter()
                .map(|l| l.into())
                .chain(once(Var::CONST)),
        );
        for cls in self.cls.iter() {
            for l in cls.iter() {
                domain.insert(l.var());
            }
        }
        let mut domain = Vec::from_iter(domain);
        domain.sort();
        let mut domain_map = VarVMap::new();
        for (i, d) in domain.iter().enumerate() {
            domain_map.insert(*d, Var::new(i));
        }
        let map_lit = |l: &Lit| l.map_var(|v| domain_map[v]);
        for cls in self.cls.iter_mut() {
            for l in cls.iter_mut() {
                *l = map_lit(l);
            }
        }
        self.max_var = Var::new(domain.len() - 1);
        domain_map
    }

    pub fn set_cls(&mut self, cls: Vec<impl Into<LitFixedVec>>) {
        self.cls = cls.into_iter().map(Into::into).collect();
        // In-place collection may keep the larger LitVec allocation.
        self.cls.shrink_to_fit();
    }

    /// Move the clauses out while retaining the variable domain.
    pub fn take_clauses(&mut self) -> Vec<LitFixedVec> {
        std::mem::take(&mut self.cls)
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
            self.add_clauses(LitVvec::cnf_and(n, &and));
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
            self.add_clauses(LitVvec::cnf_or(n, &or));
            n
        }
    }
}

impl Deref for Cnf {
    type Target = [LitFixedVec];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.cls
    }
}

impl DerefMut for Cnf {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cls
    }
}

impl Default for Cnf {
    fn default() -> Self {
        Self {
            max_var: Var(0),
            cls: vec![LitFixedVec::from([Lit::TRUE])],
        }
    }
}

impl DagCnf {
    #[inline]
    pub fn lower(&self) -> Cnf {
        Cnf {
            max_var: self.max_var(),
            cls: self.clause().cloned().collect(),
        }
    }
}
