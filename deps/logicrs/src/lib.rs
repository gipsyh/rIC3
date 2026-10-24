mod assign;
mod cnf;
mod cstdagcnf;
mod dagcnf;
pub mod dimacs;
pub mod fol;
mod lbool;
mod litordvec;
mod litvec;
mod litvvec;
mod occur;
pub mod satif;
mod utils;

pub use assign::*;
pub use cnf::*;
pub use cstdagcnf::*;
pub use dagcnf::*;
pub use lbool::*;
pub use litordvec::*;
pub use litvec::*;
pub use litvvec::*;
use serde::{Deserialize, Serialize};
pub use utils::*;

use std::{
    fmt::{self, Debug, Display},
    hash::Hash,
    ops::{Add, AddAssign, Deref, Not, Sub},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Var(pub u32);

impl Var {
    pub const CONST: Var = Var(0);
    pub const NONE: Var = Var(u32::MAX);

    #[inline]
    pub const fn new(x: usize) -> Self {
        Self(x as _)
    }

    #[inline]
    pub const fn lit(&self) -> Lit {
        debug_assert!(!self.is_none());
        Lit(self.0 << 1)
    }

    #[inline]
    pub const fn is_constant(&self) -> bool {
        self.0 == Self::CONST.0
    }

    #[inline]
    pub const fn is_none(&self) -> bool {
        self.0 == Self::NONE.0
    }
}

impl Default for Var {
    #[inline]
    fn default() -> Self {
        Self::NONE
    }
}

impl Add<Var> for Var {
    type Output = Var;

    #[inline]
    fn add(self, rhs: Var) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Sub<Var> for Var {
    type Output = Var;

    #[inline]
    fn sub(self, rhs: Var) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl AddAssign<Var> for Var {
    #[inline]
    fn add_assign(&mut self, rhs: Var) {
        self.0 += rhs.0;
    }
}

impl From<Lit> for Var {
    #[inline]
    fn from(value: Lit) -> Self {
        value.var()
    }
}

impl From<&Lit> for Var {
    #[inline]
    fn from(value: &Lit) -> Self {
        value.var()
    }
}

impl Deref for Var {
    type Target = u32;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<Var> for Var {
    #[inline]
    fn as_ref(&self) -> &Var {
        self
    }
}

impl AsMut<Var> for Var {
    #[inline]
    fn as_mut(&mut self) -> &mut Var {
        self
    }
}

impl From<&Var> for Var {
    #[inline]
    fn from(value: &Var) -> Self {
        *value
    }
}

impl Display for Var {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_none() {
            write!(f, "NoneVar")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl Debug for Var {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}

macro_rules! impl_var_traits {
    ($T:ty) => {
        impl PartialEq<$T> for Var {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                self.0.eq(&(*other as u32))
            }
        }

        impl PartialOrd<$T> for Var {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&(*other as u32))
            }
        }

        impl From<Var> for $T {
            #[inline]
            fn from(value: Var) -> Self {
                value.0 as $T
            }
        }

        impl From<$T> for Var {
            #[inline]
            fn from(value: $T) -> Self {
                Self(value as u32)
            }
        }

        impl Add<$T> for Var {
            type Output = Var;

            #[inline]
            fn add(self, rhs: $T) -> Self::Output {
                Self(self.0 + rhs as u32)
            }
        }

        impl Sub<$T> for Var {
            type Output = Var;

            #[inline]
            fn sub(self, rhs: $T) -> Self::Output {
                Self(self.0 - rhs as u32)
            }
        }

        impl AddAssign<$T> for Var {
            #[inline]
            fn add_assign(&mut self, rhs: $T) {
                self.0 += rhs as u32;
            }
        }
    };
}

impl_var_traits!(u32);
impl_var_traits!(i32);
impl_var_traits!(usize);
impl_var_traits!(isize);

/// An iterator over a range of `Var` values (stable Rust compatible replacement for RangeInclusive<Var>)
#[derive(Clone, Debug)]
pub struct VarRange {
    inner: std::ops::RangeInclusive<u32>,
}

impl VarRange {
    #[inline]
    pub fn new_inclusive(start: Var, end: Var) -> Self {
        Self {
            inner: start.0..=end.0,
        }
    }
}

impl Iterator for VarRange {
    type Item = Var;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Var)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl DoubleEndedIterator for VarRange {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(Var)
    }
}

impl ExactSizeIterator for VarRange {}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Lit(u32);

impl From<Var> for Lit {
    #[inline]
    fn from(value: Var) -> Self {
        value.lit()
    }
}

impl From<Lit> for u32 {
    #[inline]
    fn from(val: Lit) -> Self {
        val.0
    }
}

impl From<Lit> for i32 {
    #[inline]
    fn from(val: Lit) -> Self {
        debug_assert!(!val.is_none());
        let mut v: i32 = val.var().into();
        if !val.polarity() {
            v = -v;
        }
        v
    }
}

impl From<i32> for Lit {
    #[inline]
    fn from(value: i32) -> Self {
        Self::new(Var(value.unsigned_abs()), value > 0)
    }
}

impl Lit {
    pub const NONE: Lit = Lit(u32::MAX);
    pub const TRUE: Lit = Lit::constant(true);
    pub const FALSE: Lit = Lit::constant(false);

    #[inline]
    pub const fn is_none(&self) -> bool {
        self.0 == Self::NONE.0
    }

    #[inline]
    pub const fn new(var: Var, polarity: bool) -> Self {
        debug_assert!(!var.is_none());
        Lit(var.0 + var.0 + !polarity as u32)
    }

    #[inline]
    pub const fn var(&self) -> Var {
        debug_assert!(!self.is_none());
        Var(self.0 >> 1)
    }

    #[inline]
    pub const fn polarity(&self) -> bool {
        debug_assert!(!self.is_none());
        self.0 & 1 == 0
    }

    #[inline]
    pub const fn constant(polarity: bool) -> Self {
        Self::new(Var::CONST, !polarity)
    }

    #[inline]
    pub fn try_constant(&self) -> Option<bool> {
        self.var().is_constant().then_some(self.is_constant(true))
    }

    #[inline]
    pub fn is_constant(&self, polarity: bool) -> bool {
        *self == Self::constant(polarity)
    }

    #[inline]
    pub fn not_if(&self, c: bool) -> Self {
        if c { !*self } else { *self }
    }

    #[inline]
    pub fn cube(&self) -> LitVec {
        LitVec::from([*self])
    }

    #[inline]
    pub fn map_var(&self, map: impl Fn(Var) -> Var) -> Self {
        Self::new(map(self.var()), self.polarity())
    }

    #[inline]
    pub fn filter_map_var(&self, map: impl Fn(Var) -> Option<Var>) -> Option<Self> {
        map(self.var()).map(|v| Self::new(v, self.polarity()))
    }
}

impl Not for Lit {
    type Output = Self;

    #[inline]
    fn not(mut self) -> Self::Output {
        debug_assert!(!self.is_none());
        self.0 ^= 1;
        self
    }
}

impl Not for &Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Self::Output {
        !*self
    }
}

impl AsRef<Lit> for Lit {
    #[inline]
    fn as_ref(&self) -> &Lit {
        self
    }
}

impl Default for Lit {
    #[inline]
    fn default() -> Self {
        Self::NONE
    }
}

impl AsMut<Lit> for Lit {
    #[inline]
    fn as_mut(&mut self) -> &mut Lit {
        self
    }
}

impl From<&Lit> for Lit {
    #[inline]
    fn from(value: &Lit) -> Self {
        *value
    }
}

impl Debug for Lit {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_none() {
            write!(f, "NoneLit")
        } else if self.polarity() {
            write!(f, "{}", self.var())
        } else {
            write!(f, "-{}", self.var())
        }
    }
}

impl Display for Lit {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_var_lit_none() {
        assert!(Var::NONE.is_none());
        assert!(!Var::CONST.is_none());
        assert!(!Var::new(1).is_none());

        assert!(Lit::NONE.is_none());
        assert!(!Lit::FALSE.is_none());
        assert!(!Lit::TRUE.is_none());
        assert!(!Lit::new(Var::new(1), true).is_none());
    }
}
