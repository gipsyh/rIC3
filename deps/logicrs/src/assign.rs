use crate::{Lbool, Lit, LitVec, Var, VarMap, VarRange};
use giputils::bitvec::BitVec;
use std::ops::{Deref, DerefMut, Index, IndexMut};

#[derive(Clone)]
pub struct VarAssign {
    v: VarMap<Lbool>,
}

impl VarAssign {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn new_with(var: Var) -> Self {
        let mut v = VarAssign::new();
        v.reserve(var);
        v
    }

    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.v.reserve(var)
    }

    #[inline]
    pub fn v(&self, lit: Lit) -> Lbool {
        Lbool(self.v[lit].0 ^ (!lit.polarity() as u8))
    }

    #[inline]
    pub fn vl(&self, v: Var) -> Option<Lit> {
        let val = self.v[v];
        if val == Lbool::NONE {
            None
        } else {
            Some(Lit::new(v, val.is_true()))
        }
    }

    #[inline]
    pub fn set(&mut self, lit: Lit) {
        self.v[lit] = Lbool(lit.polarity() as u8)
    }

    #[inline]
    pub fn set_none(&mut self, var: Var) {
        self.v[var] = Lbool::NONE
    }
}

impl Default for VarAssign {
    #[inline]
    fn default() -> Self {
        let v = VarMap::new();
        let mut res = Self { v };
        res.reserve(Var::CONST);
        res.set(Lit::TRUE);
        res
    }
}

#[derive(Default)]
pub struct VarBitVec {
    vbv: VarMap<BitVec>,
}

impl Index<Var> for VarBitVec {
    type Output = BitVec;

    #[inline]
    fn index(&self, var: Var) -> &Self::Output {
        &self.vbv[var]
    }
}

impl IndexMut<Var> for VarBitVec {
    #[inline]
    fn index_mut(&mut self, var: Var) -> &mut Self::Output {
        &mut self.vbv[var]
    }
}

impl Deref for VarBitVec {
    type Target = VarMap<BitVec>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.vbv
    }
}

impl DerefMut for VarBitVec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.vbv
    }
}

impl VarBitVec {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn bv_len(&self) -> usize {
        self[Var::CONST].len()
    }

    #[inline]
    pub fn val(&self, lit: Lit) -> BitVec {
        if !lit.polarity() {
            !&self.vbv[lit.var()]
        } else {
            self.vbv[lit.var()].clone()
        }
    }

    #[inline]
    pub fn assign(
        &self,
        idx: usize,
        filter: Option<impl IntoIterator<Item = impl Into<Var>>>,
    ) -> LitVec {
        let mut assump = LitVec::new();
        if let Some(filter) = filter {
            for v in filter.into_iter().map(|v| v.into()) {
                let b = self[v].get(idx);
                let l = v.lit().not_if(!b);
                assump.push(l);
            }
        } else {
            for v in VarRange::new_inclusive(Var::CONST, self.vbv.max_var()) {
                let b = self[v].get(idx);
                let l = v.lit().not_if(!b);
                assump.push(l);
            }
        }
        assump
    }
}
