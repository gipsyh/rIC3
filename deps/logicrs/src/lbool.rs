use giputils::bitvec::BitVec;
use serde::{Deserialize, Serialize};
use std::{
    fmt::{self, Debug, Display, Write},
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Lbool(pub(crate) u8);

impl Lbool {
    pub const FALSE: Lbool = Lbool(0);
    pub const TRUE: Lbool = Lbool(1);
    pub const NONE: Lbool = Lbool(2);

    #[inline]
    pub fn is_true(self) -> bool {
        self == Self::TRUE
    }

    #[inline]
    pub fn is_false(self) -> bool {
        self == Self::FALSE
    }

    #[inline]
    pub fn is_none(self) -> bool {
        self.0 & 2 != 0
    }

    #[inline]
    pub fn not_if(self, x: bool) -> Self {
        if x { !self } else { self }
    }
}

impl From<bool> for Lbool {
    #[inline]
    fn from(value: bool) -> Self {
        Self(value as u8)
    }
}

impl From<Lbool> for Option<bool> {
    #[inline]
    fn from(val: Lbool) -> Self {
        match val {
            Lbool::TRUE => Some(true),
            Lbool::FALSE => Some(false),
            _ => None,
        }
    }
}

impl Default for Lbool {
    #[inline]
    fn default() -> Self {
        Self::NONE
    }
}

impl Debug for Lbool {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let field = match *self {
            Lbool::TRUE => '1',
            Lbool::FALSE => '0',
            _ => 'X',
        };
        f.write_char(field)
    }
}

impl Display for Lbool {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl Not for Lbool {
    type Output = Self;

    #[inline]
    fn not(self) -> Self::Output {
        Lbool(self.0 ^ 1)
    }
}

impl BitAnd for Lbool {
    type Output = Lbool;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        if self.is_false() || rhs.is_false() {
            Self::FALSE
        } else if self.is_none() || rhs.is_none() {
            Self::NONE
        } else {
            Self::TRUE
        }
    }
}

impl BitOr for Lbool {
    type Output = Lbool;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        if self.is_true() || rhs.is_true() {
            Self::TRUE
        } else if self.is_none() || rhs.is_none() {
            Self::NONE
        } else {
            Self::FALSE
        }
    }
}

impl BitXor for Lbool {
    type Output = Lbool;

    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        if self.is_none() || rhs.is_none() {
            Self::NONE
        } else {
            Self(self.0 ^ rhs.0)
        }
    }
}

#[derive(Clone, Default, Serialize, Deserialize)]
pub struct LboolVec {
    v: BitVec,
    m: BitVec,
}

impl LboolVec {
    #[inline]
    pub fn from_elem(v: Lbool, len: usize) -> Self {
        Self {
            v: BitVec::from_elem(len, v.is_true()),
            m: BitVec::from_elem(len, !v.is_none()),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn all_x(&self) -> bool {
        self.mask().is_zero()
    }

    #[inline]
    pub fn any_x(&self) -> bool {
        !self.mask().is_ones()
    }

    #[inline]
    pub fn v(&self) -> &BitVec {
        &self.v
    }

    #[inline]
    pub fn mask(&self) -> &BitVec {
        &self.m
    }

    #[inline]
    pub fn get_masked(&self) -> BitVec {
        &self.v & &self.m
    }

    #[inline]
    pub fn get(&self, idx: usize) -> Lbool {
        if !self.m.get(idx) {
            Lbool::NONE
        } else {
            Lbool::from(self.v.get(idx))
        }
    }

    #[inline]
    pub fn set(&mut self, idx: usize, v: Lbool) {
        self.m.set(idx, !v.is_none());
        self.v.set(idx, v.is_true());
    }

    #[inline]
    pub fn set_bool(&mut self, idx: usize, v: bool) {
        self.m.set(idx, true);
        self.v.set(idx, v);
    }
}

impl PartialEq for LboolVec {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        if self.m != other.m {
            return false;
        }
        self.get_masked() == other.get_masked()
    }
}

impl Eq for LboolVec {}

impl Debug for LboolVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "[]");
        }
        let mut s = String::with_capacity(self.len());
        for i in (0..self.len()).rev() {
            if !self.m.get(i) {
                s.push('x');
            } else if self.v.get(i) {
                s.push('1');
            } else {
                s.push('0');
            }
        }
        write!(f, "{s}")
    }
}

impl Display for LboolVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl fmt::Binary for LboolVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl From<&str> for LboolVec {
    #[inline]
    fn from(value: &str) -> Self {
        let mut v = BitVec::new();
        let mut m = BitVec::new();
        for c in value.chars().rev() {
            match c {
                '1' => {
                    v.push(true);
                    m.push(true);
                }
                '0' => {
                    v.push(false);
                    m.push(true);
                }
                'x' | 'X' => {
                    v.push(false);
                    m.push(false);
                }
                _ => panic!("Invalid character in lbool string"),
            }
        }
        Self { v, m }
    }
}

impl From<BitVec> for LboolVec {
    fn from(v: BitVec) -> Self {
        Self {
            m: BitVec::from_elem(v.len(), true),
            v,
        }
    }
}

impl From<LboolVec> for BitVec {
    fn from(lbv: LboolVec) -> Self {
        assert!(!lbv.any_x(), "LboolVec contains X values");
        lbv.v
    }
}

impl From<&LboolVec> for BitVec {
    fn from(lbv: &LboolVec) -> Self {
        assert!(!lbv.any_x(), "LboolVec contains X values");
        lbv.v.clone()
    }
}

impl LboolVec {
    pub fn iter(&self) -> Iter<'_> {
        debug_assert_eq!(self.v.len(), self.m.len());
        Iter {
            v: &self.v,
            m: &self.m,
            start: 0,
            end: self.len(),
        }
    }
}

pub struct Iter<'a> {
    v: &'a BitVec,
    m: &'a BitVec,
    start: usize,
    end: usize,
}

impl<'a> Iterator for Iter<'a> {
    type Item = Lbool;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let idx = self.start;
            self.start += 1;
            debug_assert_eq!(self.v.len(), self.m.len());
            if !self.m.get(idx) {
                Some(Lbool::NONE)
            } else if self.v.get(idx) {
                Some(Lbool::TRUE)
            } else {
                Some(Lbool::FALSE)
            }
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end - self.start;
        (len, Some(len))
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            self.end -= 1;
            let idx = self.end;
            debug_assert_eq!(self.v.len(), self.m.len());
            if !self.m.get(idx) {
                Some(Lbool::NONE)
            } else if self.v.get(idx) {
                Some(Lbool::TRUE)
            } else {
                Some(Lbool::FALSE)
            }
        } else {
            None
        }
    }
}

impl<'a> ExactSizeIterator for Iter<'a> {}

impl<'a> IntoIterator for &'a LboolVec {
    type Item = Lbool;
    type IntoIter = Iter<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

macro_rules! impl_lboolvec_op {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        impl $trait<&LboolVec> for &LboolVec {
            type Output = LboolVec;

            fn $method(self, rhs: &LboolVec) -> Self::Output {
                assert_eq!(self.len(), rhs.len());
                let mut res = LboolVec::from_elem(Lbool::NONE, self.len());
                for i in 0..self.len() {
                    res.set(i, self.get(i).$method(rhs.get(i)));
                }
                res
            }
        }

        impl $trait<LboolVec> for &LboolVec {
            type Output = LboolVec;

            fn $method(self, rhs: LboolVec) -> Self::Output {
                self.$method(&rhs)
            }
        }

        impl $trait<&LboolVec> for LboolVec {
            type Output = LboolVec;

            fn $method(self, rhs: &LboolVec) -> Self::Output {
                (&self).$method(rhs)
            }
        }

        impl $trait<LboolVec> for LboolVec {
            type Output = LboolVec;

            fn $method(self, rhs: LboolVec) -> Self::Output {
                (&self).$method(&rhs)
            }
        }

        impl $assign_trait<&LboolVec> for LboolVec {
            fn $assign_method(&mut self, rhs: &LboolVec) {
                assert_eq!(self.len(), rhs.len());
                for i in 0..self.len() {
                    self.set(i, self.get(i).$method(rhs.get(i)));
                }
            }
        }

        impl $assign_trait<LboolVec> for LboolVec {
            fn $assign_method(&mut self, rhs: LboolVec) {
                self.$assign_method(&rhs)
            }
        }
    };
}

impl_lboolvec_op!(BitAnd, bitand, BitAndAssign, bitand_assign);
impl_lboolvec_op!(BitOr, bitor, BitOrAssign, bitor_assign);
impl_lboolvec_op!(BitXor, bitxor, BitXorAssign, bitxor_assign);

impl Not for LboolVec {
    type Output = LboolVec;

    fn not(mut self) -> Self::Output {
        self.v = !&self.v;
        self
    }
}

impl Not for &LboolVec {
    type Output = LboolVec;

    fn not(self) -> Self::Output {
        let mut res = self.clone();
        res.v = !&self.v;
        res
    }
}
