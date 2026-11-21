use crate::{Lit, LitOrdVec, LitVec, lemmas_subsume_simplify};
use derive_more::{Deref, DerefMut, From, IntoIterator};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Default, Serialize, Deserialize, Deref, DerefMut, IntoIterator, From)]
#[into_iterator(owned, ref)]
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

impl FromIterator<LitVec> for LitVvec {
    #[inline]
    fn from_iter<I: IntoIterator<Item = LitVec>>(iter: I) -> Self {
        Self {
            vec: Vec::from_iter(iter),
        }
    }
}
