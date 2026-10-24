use super::{Term, op::FolOp};
use std::{
    ops::{Deref, DerefMut, Index, IndexMut, Range, RangeFrom, RangeInclusive, RangeTo},
    slice, vec,
};

#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct TermVec {
    data: Vec<Term>,
}

impl TermVec {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn item(mut self) -> Term {
        self.data.pop().unwrap()
    }

    #[inline]
    pub fn fold(&self, op: FolOp) -> Term {
        Term::new_op_fold(op, self.iter())
    }

    // #[inline]
    // pub fn ordered_subsume(&self, cube: &TermCube) -> bool {
    //     debug_assert!(self.is_sorted());
    //     debug_assert!(cube.is_sorted());
    //     if self.len() > cube.len() {
    //         return false;
    //     }
    //     let mut j = 0;
    //     for i in 0..self.len() {
    //         while j < cube.len() && self[i] > cube[j] {
    //             j += 1;
    //         }
    //         if j == cube.len() || self[i] != cube[j] {
    //             return false;
    //         }
    //     }
    //     true
    // }
}

impl Deref for TermVec {
    type Target = Vec<Term>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl DerefMut for TermVec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl Index<usize> for TermVec {
    type Output = Term;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.data[index]
    }
}

impl IndexMut<usize> for TermVec {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.data[index]
    }
}

impl Index<Range<usize>> for TermVec {
    type Output = [Term];

    #[inline]
    fn index(&self, index: Range<usize>) -> &Self::Output {
        self.data.index(index)
    }
}

impl Index<RangeTo<usize>> for TermVec {
    type Output = [Term];

    #[inline]
    fn index(&self, index: RangeTo<usize>) -> &Self::Output {
        self.data.index(index)
    }
}

impl Index<RangeFrom<usize>> for TermVec {
    type Output = [Term];
    #[inline]
    fn index(&self, index: RangeFrom<usize>) -> &Self::Output {
        self.data.index(index)
    }
}

impl Index<RangeInclusive<usize>> for TermVec {
    type Output = [Term];

    #[inline]
    fn index(&self, index: RangeInclusive<usize>) -> &Self::Output {
        self.data.index(index)
    }
}

impl FromIterator<Term> for TermVec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = Term>>(iter: T) -> Self {
        Self {
            data: Vec::from_iter(iter),
        }
    }
}

impl IntoIterator for TermVec {
    type Item = Term;
    type IntoIter = vec::IntoIter<Term>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}

impl<'a> IntoIterator for &'a TermVec {
    type Item = &'a Term;
    type IntoIter = slice::Iter<'a, Term>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.data.iter()
    }
}

impl From<&[Term]> for TermVec {
    #[inline]
    fn from(value: &[Term]) -> Self {
        Self {
            data: Vec::from(value),
        }
    }
}

impl<const N: usize> From<[Term; N]> for TermVec {
    #[inline]
    fn from(value: [Term; N]) -> Self {
        Self {
            data: Vec::from(value),
        }
    }
}

impl From<Vec<Term>> for TermVec {
    #[inline]
    fn from(value: Vec<Term>) -> Self {
        Self { data: value }
    }
}

/// Type alias for optional Term result (stable Rust compatible)
pub type TermResult = Option<Term>;
