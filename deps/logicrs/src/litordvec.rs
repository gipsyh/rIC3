use crate::{Lit, LitSet, LitVec};
use ahash::AHasher;
use std::hash::{Hash, Hasher};
use std::slice;
use std::{
    cmp::Ordering,
    fmt::{self, Display},
    ops::{Deref, DerefMut},
};

#[derive(Debug, Default, Clone)]
pub struct LitOrdVec {
    cube: LitVec,
    sign: u128,
    hash: u64,
}

impl Deref for LitOrdVec {
    type Target = LitVec;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.cube
    }
}

impl DerefMut for LitOrdVec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cube
    }
}

impl PartialEq for LitOrdVec {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if self.hash != other.hash || self.sign != other.sign || self.len() != other.len() {
            return false;
        }
        for i in 0..self.cube.len() {
            if self[i] != other[i] {
                return false;
            }
        }
        true
    }
}

impl Eq for LitOrdVec {}

impl PartialOrd for LitOrdVec {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LitOrdVec {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.cube.cmp(&other.cube)
    }
}

impl LitOrdVec {
    #[inline]
    pub fn new(mut lv: LitVec) -> Self {
        lv.sort();
        let mut sign = 0;
        for l in lv.iter() {
            sign |= 1 << (Into::<u32>::into(*l) % u128::BITS);
        }
        let mut hasher = AHasher::default();
        lv.hash(&mut hasher);
        Self {
            cube: lv,
            sign,
            hash: hasher.finish(),
        }
    }

    #[inline]
    pub fn as_litvec(&self) -> &LitVec {
        &self.cube
    }

    #[inline]
    pub fn into_litvec(self) -> LitVec {
        self.cube
    }

    #[inline]
    fn var_sign(&self) -> u128 {
        ((self.sign >> 1) | self.sign) & 113427455640312821154458202477256070485_u128
    }

    #[inline]
    pub fn subsume(&self, other: &LitOrdVec) -> bool {
        if self.cube.len() > other.cube.len() {
            return false;
        }
        if self.sign & other.sign != self.sign {
            return false;
        }
        self.cube.ordered_subsume(&other.cube)
    }

    #[inline]
    pub fn subsume_execpt_one(&self, other: &LitOrdVec) -> (bool, Option<Lit>) {
        if self.cube.len() > other.cube.len() {
            return (false, None);
        }
        let ss = self.var_sign();
        if ss & other.var_sign() != ss {
            return (false, None);
        }
        self.cube.ordered_subsume_execpt_one(&other.cube)
    }

    #[inline]
    pub fn subsume_set(&self, other: &LitOrdVec, other_lits: &LitSet) -> bool {
        if self.cube.len() > other.cube.len() {
            return false;
        }
        if self.sign & other.sign != self.sign {
            return false;
        }
        for l in self.iter() {
            if !other_lits.has(*l) {
                return false;
            }
        }
        true
    }
}

impl Hash for LitOrdVec {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

impl Display for LitOrdVec {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.cube, f)
    }
}

pub fn lemmas_subsume_simplify(mut lemmas: Vec<LitOrdVec>) -> Vec<LitOrdVec> {
    lemmas.sort_by_key(|l| l.len());
    let mut i = 0;
    while i < lemmas.len() {
        if lemmas[i].is_empty() {
            i += 1;
            continue;
        }
        let mut update = false;
        for j in i + 1..lemmas.len() {
            if lemmas[j].is_empty() {
                continue;
            }
            let (res, diff) = lemmas[i].subsume_execpt_one(&lemmas[j]);
            if res {
                lemmas[j] = Default::default();
                continue;
            } else if let Some(diff) = diff {
                if lemmas[i].len() == lemmas[j].len() {
                    update = true;
                    let mut cube = lemmas[i].as_litvec().clone();
                    cube.retain(|l| *l != diff);
                    lemmas[i] = LitOrdVec::new(cube);
                    lemmas[j] = Default::default();
                } else {
                    let mut cube = lemmas[j].as_litvec().clone();
                    cube.retain(|l| *l != !diff);
                    lemmas[j] = LitOrdVec::new(cube);
                }
            }
        }
        if !update {
            i += 1;
        }
    }
    lemmas.retain(|l| !l.is_empty());
    lemmas
}

impl IntoIterator for LitOrdVec {
    type Item = Lit;
    type IntoIter = std::vec::IntoIter<Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.cube.clone().into_iter()
    }
}

impl<'a> IntoIterator for &'a LitOrdVec {
    type Item = &'a Lit;
    type IntoIter = slice::Iter<'a, Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.cube.iter()
    }
}

impl<T: Into<LitVec>> From<T> for LitOrdVec {
    #[inline]
    fn from(lv: T) -> Self {
        Self::new(lv.into())
    }
}
