use crate::{Lit, LitOrdVec, LitVec, lemmas_subsume_simplify};
use serde::{Deserialize, Serialize};
use std::{
    ops::{Deref, DerefMut},
    slice, vec,
};

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LitVvec {
    vec: Vec<LitVec>,
}

impl LitVvec {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn cnf_and(n: Lit, lits: &[Lit]) -> Self {
        let mut vec = Vec::with_capacity(lits.len() + 1);
        let mut cls = LitVec::new_with_cap(lits.len() + 1);
        cls.push(n);
        for l in lits.iter() {
            vec.push(LitVec::from([!n, *l]));
            cls.push(!*l);
        }
        vec.push(cls);
        Self { vec }
    }

    #[inline]
    pub fn cnf_or(n: Lit, lits: &[Lit]) -> Self {
        let mut vec = Vec::with_capacity(lits.len() + 1);
        let mut cls = LitVec::new_with_cap(lits.len() + 1);
        cls.push(!n);
        for l in lits.iter() {
            vec.push(LitVec::from([n, !*l]));
            cls.push(*l);
        }
        vec.push(cls);
        Self { vec }
    }

    #[inline]
    pub fn cnf_assign(n: Lit, s: Lit) -> Self {
        Self {
            vec: vec![LitVec::from([n, !s]), LitVec::from([!n, s])],
        }
    }

    #[inline]
    pub fn cnf_xor(n: Lit, x: Lit, y: Lit) -> Self {
        Self {
            vec: vec![
                LitVec::from([!x, y, n]),
                LitVec::from([x, !y, n]),
                LitVec::from([x, y, !n]),
                LitVec::from([!x, !y, !n]),
            ],
        }
    }

    #[inline]
    pub fn cnf_xnor(n: Lit, x: Lit, y: Lit) -> Self {
        Self {
            vec: vec![
                LitVec::from([!x, y, !n]),
                LitVec::from([x, !y, !n]),
                LitVec::from([x, y, n]),
                LitVec::from([!x, !y, n]),
            ],
        }
    }

    #[inline]
    pub fn cnf_ite(n: Lit, c: Lit, t: Lit, e: Lit) -> Self {
        Self {
            vec: vec![
                LitVec::from([t, !c, !n]),
                LitVec::from([!t, !c, n]),
                LitVec::from([e, c, !n]),
                LitVec::from([!e, c, n]),
            ],
        }
    }

    pub fn subsume_simplify(&mut self) {
        let res: Vec<_> = self.iter().map(|l| LitOrdVec::new(l.clone())).collect();
        self.vec = lemmas_subsume_simplify(res)
            .into_iter()
            .map(|l| l.into_litvec())
            .collect();
    }

    #[inline]
    pub fn num_lit(&self) -> usize {
        self.iter().map(|l| l.len()).sum()
    }
}

impl Deref for LitVvec {
    type Target = Vec<LitVec>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.vec
    }
}

impl DerefMut for LitVvec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.vec
    }
}

impl IntoIterator for LitVvec {
    type Item = LitVec;
    type IntoIter = vec::IntoIter<LitVec>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}

impl<'a> IntoIterator for &'a LitVvec {
    type Item = &'a LitVec;
    type IntoIter = slice::Iter<'a, LitVec>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.vec.iter()
    }
}

impl FromIterator<LitVec> for LitVvec {
    #[inline]
    fn from_iter<I: IntoIterator<Item = LitVec>>(iter: I) -> Self {
        Self {
            vec: Vec::from_iter(iter),
        }
    }
}

impl From<Vec<LitVec>> for LitVvec {
    fn from(vec: Vec<LitVec>) -> Self {
        Self { vec }
    }
}
