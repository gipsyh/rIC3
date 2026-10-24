use crate::gvec::Gvec;
use core::panic;
use rand::rngs::StdRng;
use serde::{Deserialize, Serialize};
use std::{
    fmt::{self, Debug, Display},
    hash::Hash,
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign,
        Bound::{Excluded, Included, Unbounded},
        Not, RangeBounds,
    },
};

#[derive(Clone, Serialize, Deserialize)]
pub struct BitVec {
    bits: Gvec<u64>,
    last_len: usize,
}

impl BitVec {
    pub const WORD_SIZE: usize = 64;
    pub const WORD_SIZE_MASK: usize = Self::WORD_SIZE - 1;

    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn new_rand(num_word: usize, rng: &mut StdRng) -> Self {
        if num_word == 0 {
            return Self::default();
        }
        Self {
            bits: Gvec::new_rand(num_word, rng),
            last_len: 64,
        }
    }

    #[inline]
    pub fn from_elem(len: usize, val: bool) -> Self {
        if len == 0 {
            return Self::default();
        }
        let v = if val { u64::MAX } else { 0 };
        let mut bits = Gvec::from(vec![v; len / Self::WORD_SIZE]);
        let mut last_len = len & Self::WORD_SIZE_MASK;
        if last_len == 0 {
            last_len = 64;
        } else {
            bits.push(if val { (1 << last_len) - 1 } else { 0 });
        }
        Self { bits, last_len }
    }

    pub fn from_usize(len: usize, v: usize) -> Self {
        if len == 0 {
            return Self::default();
        }
        let mut res = Self::zero(len);
        res.bits[0] = v as u64;
        res.mask_last();
        res
    }

    pub fn to_usize(&self) -> usize {
        assert!(self.len() as u32 <= usize::BITS);
        if self.is_empty() {
            return 0;
        }
        self.bits[0usize] as usize
    }

    #[inline]
    pub fn len(&self) -> usize {
        (self.bits.len() - 1) * 64 + self.last_len
    }

    #[inline]
    pub fn word_len(&self) -> usize {
        let mut res = self.bits.len();
        if self.last_len == 0 {
            res -= 1
        }
        res
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn clear(&mut self) {
        *self = Self::default();
    }

    #[inline]
    pub fn get(&self, index: usize) -> bool {
        debug_assert!(index < self.len());
        let word_index = index / 64;
        let bit_index = index % 64;
        let mask = 1 << bit_index;
        (self.bits[word_index] & mask) != 0
    }

    #[inline]
    pub fn set(&mut self, index: usize, val: bool) {
        debug_assert!(index < self.len());
        let word_index = index / 64;
        let bit_index = index % 64;
        let mask = 1 << bit_index;
        if val {
            self.bits[word_index] |= mask;
        } else {
            self.bits[word_index] &= !mask;
        }
    }

    /// Returns the bits in `range`, using the same bounds semantics as Rust ranges.
    #[inline]
    pub fn slice<R: RangeBounds<usize>>(&self, range: R) -> Self {
        let l = match range.start_bound() {
            Included(&l) => l,
            Excluded(&l) => l.checked_add(1).expect("range start overflows usize"),
            Unbounded => 0,
        };
        let h = match range.end_bound() {
            Included(&h) => h.checked_add(1).expect("range end overflows usize"),
            Excluded(&h) => h,
            Unbounded => self.len(),
        };

        debug_assert!(l <= h);
        debug_assert!(h <= self.len());
        let mut res = BitVec::zero(h - l);
        for idx in l..h {
            res.set(idx - l, self.get(idx));
        }
        res
    }

    #[inline]
    #[allow(unused)]
    fn last_word(&self) -> &u64 {
        unsafe { self.bits.last().unwrap_unchecked() }
    }

    #[inline]
    fn last_word_mut(&mut self) -> &mut u64 {
        unsafe { self.bits.last_mut().unwrap_unchecked() }
    }

    #[inline]
    fn mask_last(&mut self) {
        if self.last_len == 64 {
            return;
        }
        let mask = (1 << self.last_len) - 1;
        *self.last_word_mut() &= mask;
    }

    #[inline]
    pub fn push(&mut self, bit: bool) {
        if self.last_len == 64 {
            self.bits.push(0);
            self.last_len = 0;
        }
        let mask = 1 << self.last_len;
        let x = self.last_word_mut();
        if bit {
            *x |= mask;
        } else {
            *x &= !mask;
        }
        self.last_len += 1;
    }
    #[inline]
    pub fn push_word(&mut self, word: u64) {
        if self.last_len == 0 {
            let l = self.bits.len() - 1;
            self.bits[l] = word;
            self.last_len = 64;
        } else if self.last_len == 64 {
            self.bits.push(word);
        } else {
            panic!();
        }
    }

    #[inline]
    pub fn zero(len: usize) -> Self {
        Self::from_elem(len, false)
    }

    #[inline]
    pub fn ones(len: usize) -> Self {
        debug_assert!(len > 0);
        Self::from_elem(len, true)
    }

    #[inline]
    pub fn one(len: usize) -> Self {
        debug_assert!(len > 0);
        let mut r = Self::from_elem(len, false);
        r.set(0, true);
        r
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        debug_assert!(!self.is_empty());
        for i in 0..self.word_len() {
            if self.bits[i] != 0 {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn is_one(&self) -> bool {
        debug_assert!(!self.is_empty());
        if self.bits[0] != 1u64 {
            return false;
        }
        for i in 1..self.word_len() {
            if self.bits[i] != 0 {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn is_ones(&self) -> bool {
        debug_assert!(!self.is_empty());
        let wl = self.word_len();
        for i in 0..wl - 1 {
            if self.bits[i] != u64::MAX {
                return false;
            }
        }
        let mask = if self.last_len == 64 {
            u64::MAX
        } else {
            (1u64 << self.last_len) - 1
        };
        self.bits[wl - 1] == mask
    }

    pub fn iter(&self) -> Iter<'_> {
        Iter {
            bv: self,
            start: 0,
            end: self.len(),
        }
    }

    #[inline]
    pub fn bool(&self) -> bool {
        if self.len() == 1 {
            self.get(0)
        } else {
            panic!();
        }
    }

    #[inline]
    pub fn try_bool(&self) -> Option<bool> {
        (self.len() == 1).then(|| self.get(0))
    }

    #[inline]
    pub fn sign_bit(&self) -> bool {
        self.get(self.len() - 1)
    }
}

impl AsRef<Self> for BitVec {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl AsMut<Self> for BitVec {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

pub struct Iter<'a> {
    bv: &'a BitVec,
    start: usize,
    end: usize,
}

impl<'a> Iterator for Iter<'a> {
    type Item = bool;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let res = self.bv.get(self.start);
            self.start += 1;
            Some(res)
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
            Some(self.bv.get(self.end))
        } else {
            None
        }
    }
}

impl<'a> ExactSizeIterator for Iter<'a> {}

impl<'a> IntoIterator for &'a BitVec {
    type Item = bool;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct IntoIter {
    bv: BitVec,
    start: usize,
    end: usize,
}

impl Iterator for IntoIter {
    type Item = bool;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let res = self.bv.get(self.start);
            self.start += 1;
            Some(res)
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

impl DoubleEndedIterator for IntoIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            self.end -= 1;
            Some(self.bv.get(self.end))
        } else {
            None
        }
    }
}

impl ExactSizeIterator for IntoIter {}

impl IntoIterator for BitVec {
    type Item = bool;
    type IntoIter = IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();
        IntoIter {
            bv: self,
            start: 0,
            end: len,
        }
    }
}

impl Default for BitVec {
    #[inline]
    fn default() -> Self {
        Self {
            bits: Gvec::from([0]),
            last_len: 0,
        }
    }
}

impl PartialEq for BitVec {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for i in 0..self.word_len() {
            if self.bits[i] != other.bits[i] {
                return false;
            }
        }
        true
    }
}

impl Eq for BitVec {}

impl Hash for BitVec {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for &bit in self.bits.iter().take(self.word_len()) {
            bit.hash(state);
        }
        (self.last_len & Self::WORD_SIZE_MASK).hash(state);
    }
}

impl Not for &BitVec {
    type Output = BitVec;

    #[inline]
    fn not(self) -> BitVec {
        let mut res = self.clone();
        for r in res.bits.iter_mut() {
            *r = !*r;
        }
        res.mask_last();
        res
    }
}

macro_rules! impl_bitop_owned_and_ref {
    (
        trait = $trait:ident,
        method = $method:ident,
        op = $op:tt,
    ) => {
        impl<R: AsRef<BitVec>> $trait<R> for BitVec {
            type Output = BitVec;

            #[inline]
            fn $method(self, rhs: R) -> Self::Output {
                assert!(self.len() == rhs.as_ref().len());
                let mut res = BitVec {
                    bits: self
                        .bits
                        .iter()
                        .zip(rhs.as_ref().bits.iter())
                        .map(|(s, r)| s $op r)
                        .collect(),
                    last_len: self.last_len,
                };
                res.mask_last();
                res
            }
        }

        impl<R: AsRef<BitVec>> $trait<R> for &BitVec {
            type Output = BitVec;

            #[inline]
            fn $method(self, rhs: R) -> Self::Output {
                assert!(self.len() == rhs.as_ref().len());
                let mut res = BitVec {
                    bits: self
                        .bits
                        .iter()
                        .zip(rhs.as_ref().bits.iter())
                        .map(|(s, r)| s $op r)
                        .collect(),
                    last_len: self.last_len,
                };
                res.mask_last();
                res
            }
        }
    };
}

macro_rules! impl_bitassign_ref {
    (
        trait = $trait:ident,
        method = $method:ident,
        op = $op:tt,
    ) => {
        impl $trait<&BitVec> for BitVec {
            #[inline]
            fn $method(&mut self, rhs: &BitVec) {
                assert!(self.len() == rhs.len());
                for (s, r) in self.bits.iter_mut().zip(rhs.bits.iter()) {
                    *s $op r;
                }
                self.mask_last();
            }
        }
    };
}

impl_bitop_owned_and_ref!(
    trait = BitAnd,
    method = bitand,
    op = &,
);

impl_bitop_owned_and_ref!(
    trait = BitOr,
    method = bitor,
    op = |,
);

impl_bitop_owned_and_ref!(
    trait = BitXor,
    method = bitxor,
    op = ^,
);

impl_bitassign_ref!(
    trait = BitAndAssign,
    method = bitand_assign,
    op = &=,
);

impl_bitassign_ref!(
    trait = BitOrAssign,
    method = bitor_assign,
    op = |=,
);

impl_bitassign_ref!(
    trait = BitXorAssign,
    method = bitxor_assign,
    op = ^=,
);

impl<const N: usize> From<[bool; N]> for BitVec {
    #[inline]
    fn from(s: [bool; N]) -> Self {
        let mut r = Self::new();
        for x in s.into_iter() {
            r.push(x);
        }
        r
    }
}

impl<const N: usize> From<&[bool; N]> for BitVec {
    #[inline]
    fn from(s: &[bool; N]) -> Self {
        let mut r = Self::new();
        for x in s {
            r.push(*x);
        }
        r
    }
}

impl From<&[bool]> for BitVec {
    #[inline]
    fn from(s: &[bool]) -> Self {
        let mut r = Self::new();
        for x in s.iter() {
            r.push(*x);
        }
        r
    }
}

impl From<&Vec<bool>> for BitVec {
    #[inline]
    fn from(s: &Vec<bool>) -> Self {
        let mut r = Self::new();
        for x in s.iter() {
            r.push(*x);
        }
        r
    }
}

impl From<&str> for BitVec {
    #[inline]
    fn from(value: &str) -> Self {
        let mut r = Self::new();
        for c in value.chars().rev() {
            match c {
                '1' => r.push(true),
                '0' => r.push(false),
                _ => panic!("Invalid character in bit string"),
            }
        }
        r
    }
}

impl FromIterator<bool> for BitVec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut r = Self::new();
        for x in iter.into_iter() {
            r.push(x);
        }
        r
    }
}

impl<'a> FromIterator<&'a bool> for BitVec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = &'a bool>>(iter: T) -> Self {
        let mut r = Self::new();
        for x in iter.into_iter() {
            r.push(*x);
        }
        r
    }
}

impl Extend<bool> for BitVec {
    fn extend<T: IntoIterator<Item = bool>>(&mut self, iter: T) {
        for x in iter {
            self.push(x);
        }
    }
}

impl<'a> Extend<&'a bool> for BitVec {
    fn extend<T: IntoIterator<Item = &'a bool>>(&mut self, iter: T) {
        for x in iter {
            self.push(*x);
        }
    }
}

impl Debug for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "[]");
        }
        let mut s = String::new();
        for i in (0..self.len()).rev() {
            if self.get(i) {
                s.push('1');
            } else {
                s.push('0');
            }
        }
        write!(f, "{s}")
    }
}

impl Display for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl fmt::LowerHex for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "[]");
        }
        write!(f, "0x")?;
        if self.is_zero() {
            return write!(f, "0");
        }
        let wl = self.word_len();
        write!(f, "{:x}", self.bits[wl - 1])?;
        for i in (0..wl - 1).rev() {
            write!(f, "{:016x}", self.bits[i])?;
        }
        Ok(())
    }
}

impl fmt::UpperHex for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "[]");
        }
        write!(f, "0x")?;
        if self.is_zero() {
            return write!(f, "0");
        }
        let wl = self.word_len();
        write!(f, "{:X}", self.bits[wl - 1])?;
        for i in (0..wl - 1).rev() {
            write!(f, "{:016X}", self.bits[i])?;
        }
        Ok(())
    }
}

impl fmt::Binary for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::GHashSet;

    #[test]
    fn test0() {
        let v = [true, false, true, false, true];
        let bv = BitVec::from(v);
        for i in 0..bv.len() {
            assert_eq!(bv.get(i), v[i]);
        }
    }

    #[test]
    fn test1() {
        let bv = BitVec::from_elem(0, true);
        assert!(bv.is_empty());
    }

    #[test]
    fn test2() {
        for w in 1..200 {
            let one = BitVec::one(w);
            assert!(one.is_one());
            let ones = BitVec::ones(w);
            assert!(ones.is_ones());
            let zero = BitVec::zero(w);
            assert!(zero.is_zero());
        }
    }

    #[test]
    fn test3() {
        let v = 12345;
        let bv = BitVec::from_usize(64, v);
        assert_eq!(bv.to_usize(), v);
        let bv2 = BitVec::from_usize(10, v);
        assert_eq!(bv2.to_usize(), v & ((1 << 10) - 1));
    }

    #[test]
    fn test4() {
        let v = [true, false, true, true, false];
        let bv = BitVec::from(v);
        let mut iter = bv.iter();
        for &val in &v {
            assert_eq!(iter.next(), Some(val));
        }
        assert_eq!(iter.next(), None);
        for (i, val) in bv.into_iter().enumerate() {
            assert_eq!(val, v[i]);
        }
    }

    #[test]
    fn test_fmt() {
        let z = BitVec::new();
        assert_eq!(format!("{}", z), "[]");
        assert_eq!(format!("{:x}", z), "[]");
        assert_eq!(format!("{:X}", z), "[]");

        let v = 12345;
        let bv = BitVec::from_usize(64, v);
        let s = format!("{}", bv);
        assert_eq!(s.len(), 64);
        assert!(s.ends_with("11000000111001"));

        assert_eq!(format!("{:x}", bv), "0x3039");
        assert_eq!(format!("{:X}", bv), "0x3039");

        let mut bv_large = BitVec::zero(128);
        bv_large.bits[0] = u64::MAX;
        bv_large.bits[1] = 1_u64;

        assert_eq!(format!("{:x}", bv_large), "0x1ffffffffffffffff");
        assert_eq!(format!("{:X}", bv_large), "0x1FFFFFFFFFFFFFFFF");

        let s_large = format!("{}", bv_large);
        assert_eq!(s_large.len(), 128);
        let expected_suffix = "1".repeat(65);
        assert!(s_large.ends_with(&expected_suffix));
        assert!(s_large.starts_with('0'));
    }

    #[test]
    fn test_extend() {
        let mut bv = BitVec::new();
        bv.extend([true, false, true]);
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.get(0), true);
        assert_eq!(bv.get(1), false);
        assert_eq!(bv.get(2), true);

        bv.extend(&[false, true]);
        assert_eq!(bv.len(), 5);
        assert_eq!(bv.get(3), false);
        assert_eq!(bv.get(4), true);
    }

    #[test]
    fn test_double_ended_iter() {
        let v = [true, false, true, true, false, true, false, false];
        let bv = BitVec::from(v);

        let mut iter = bv.iter();
        let mut v_iter = v.iter().copied();
        while v_iter.len() > 0 {
            if v_iter.len() % 2 == 0 {
                assert_eq!(iter.next(), v_iter.next());
            } else {
                assert_eq!(iter.next_back(), v_iter.next_back());
            }
        }
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        let mut iter = bv.clone().into_iter();
        let mut v_iter = v.iter().copied();
        while v_iter.len() > 0 {
            if v_iter.len() % 2 != 0 {
                assert_eq!(iter.next(), v_iter.next());
            } else {
                assert_eq!(iter.next_back(), v_iter.next_back());
            }
        }
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_hash_eq() {
        let a = BitVec::ones(64);
        let b = BitVec {
            bits: Gvec::from([u64::MAX, 0]),
            last_len: 0,
        };
        assert!(a == b);
        let mut s = GHashSet::new();
        s.insert(a);
        s.insert(b);
        assert!(s.len() == 1);
    }

    #[test]
    fn test_from_iter_str() {
        let bv0 = BitVec::from_usize(2, 2);
        let bv1 = BitVec::from_iter([false, true]);
        let bv2 = BitVec::from("10");
        assert!(bv0 == bv1);
        assert!(bv0 == bv2);
    }

    #[test]
    fn test_slice() {
        let bv = BitVec::from_iter((0..130).map(|i| i % 3 == 0 || i % 7 == 0));

        let cases = [
            (0, 0),
            (0, 1),
            (1, 5),
            (0, 64),
            (3, 67),
            (64, 128),
            (65, 130),
        ];
        for (l, h) in cases {
            let slice = bv.slice(l..h);
            assert_eq!(slice.len(), h - l);
            for i in 0..slice.len() {
                assert_eq!(slice.get(i), bv.get(l + i), "l={l}, h={h}, i={i}");
            }
        }

        let slice = bv.slice(3..=67);
        assert_eq!(slice.len(), 65);
        for i in 0..slice.len() {
            assert_eq!(slice.get(i), bv.get(3 + i), "inclusive range, i={i}");
        }
    }
}
