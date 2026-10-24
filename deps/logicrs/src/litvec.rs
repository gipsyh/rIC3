use crate::{Lit, Var, VarAssign};
use giputils::hash::GHashSet;
use serde::{Deserialize, Serialize};
use std::{
    alloc::{Layout, handle_alloc_error},
    cmp::Ordering,
    fmt::{self, Debug, Display},
    ops::{Deref, DerefMut, Not},
    ptr::{self, NonNull},
    slice,
};

#[repr(C)]
#[derive(Clone, Copy)]
union FixedLitData {
    len: u32,
    lit: Lit,
}

/// An owned literal slice that can shrink but cannot grow. The handle is one
/// pointer; each nonempty allocation starts with a u32 logical length.
/// Shrinking retains the allocation unless the slice becomes empty.
/// Allocation and deallocation use malloc/free.
#[derive(Default)]
pub struct LitFixedVec(Option<NonNull<FixedLitData>>);

// The allocation is uniquely owned. Shared access only exposes &[Lit], and
// mutating the literals requires exclusive access to the owner.
unsafe impl Send for LitFixedVec {}
unsafe impl Sync for LitFixedVec {}

impl LitFixedVec {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn len(&self) -> u32 {
        // SAFETY: every non-null allocation has an initialized length header.
        self.0.map_or(0, |data| unsafe { data.as_ref().len })
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    #[inline]
    pub fn last(&self) -> Lit {
        *self.as_slice().last().expect("empty literal vector")
    }

    #[inline]
    pub fn as_slice(&self) -> &[Lit] {
        self
    }

    /// Shorten the logical slice without reallocating. Truncating to zero
    /// releases the allocation; requesting a larger length has no effect.
    #[inline]
    pub fn truncate(&mut self, len: u32) {
        if len >= self.len() {
            return;
        }
        if len == 0 {
            *self = Self::new();
        } else if let Some(mut data) = self.0 {
            // SAFETY: the allocation is exclusively owned, and the new length
            // only exposes a prefix of the previously initialized literals.
            unsafe { data.as_mut().len = len };
        }
    }

    /// Remove consecutive duplicates in place, retaining the allocation.
    #[inline]
    pub fn dedup(&mut self) {
        let len = self.len() as usize;
        if len < 2 {
            return;
        }
        let mut kept = 1;
        for i in 1..len {
            if self[i] != self[kept - 1] {
                self[kept] = self[i];
                kept += 1;
            }
        }
        self.truncate(kept as u32);
    }

    /// Retain matching literals in order, without allocating another buffer.
    #[inline]
    pub fn retain(&mut self, mut f: impl FnMut(&Lit) -> bool) {
        let mut kept = 0;
        for i in 0..self.len() as usize {
            if f(&self[i]) {
                self[kept] = self[i];
                kept += 1;
            }
        }
        self.truncate(kept as u32);
    }

    /// Simplify sorted literals in place. Return None for a satisfied or
    /// tautological clause, and an empty slice for a falsified clause.
    #[inline]
    pub fn ordered_simp(mut self, v: &VarAssign) -> Option<Self> {
        let len = ordered_simp_in_place(&mut self, v)?;
        self.truncate(len as u32);
        Some(self)
    }

    #[inline]
    pub fn ordered_subsume_execpt_one(&self, cube: &Self) -> (bool, Option<Lit>) {
        ordered_subsume_except_one_slice(self, cube)
    }

    /// Build a sorted resolvent in a growable vector, without copying either
    /// source clause. Return None if the resolvent is tautological.
    #[inline]
    pub fn ordered_resolvent(&self, other: &Self, v: Var) -> Option<LitVec> {
        ordered_resolvent_slice(self, other, v)
    }

    /// Bytes occupied by the header and live literals. This is a lower bound on
    /// heap usage: it excludes space retained after shrinking and allocator overhead.
    pub fn mem_usage(&self) -> usize {
        if self.is_empty() {
            0
        } else {
            (self.len() as usize + 1) * size_of::<FixedLitData>()
        }
    }

    #[inline]
    pub fn map(&self, f: impl Fn(Lit) -> Lit) -> LitVec {
        self.iter().copied().map(f).collect()
    }
}

impl From<&[Lit]> for LitFixedVec {
    #[inline]
    fn from(lits: &[Lit]) -> Self {
        if lits.is_empty() {
            return Self::new();
        }
        let len = u32::try_from(lits.len()).expect("literal vector too long");
        let count = lits.len().checked_add(1).expect("literal vector too long");
        let layout = Layout::array::<FixedLitData>(count).expect("literal vector too long");
        // SAFETY: malloc provides sufficient alignment for FixedLitData. The
        // checked layout includes the header and every literal. No references
        // escape before the header and payload are fully initialized.
        unsafe {
            let raw = libc::malloc(layout.size()).cast::<FixedLitData>();
            let data = NonNull::new(raw).unwrap_or_else(|| handle_alloc_error(layout));
            raw.write(FixedLitData { len });
            ptr::copy_nonoverlapping(lits.as_ptr(), raw.add(1).cast::<Lit>(), lits.len());
            Self(Some(data))
        }
    }
}

impl<const N: usize> From<[Lit; N]> for LitFixedVec {
    #[inline]
    fn from(lits: [Lit; N]) -> Self {
        Self::from(lits.as_slice())
    }
}

impl From<LitVec> for LitFixedVec {
    #[inline]
    fn from(lits: LitVec) -> Self {
        Self::from(lits.as_slice())
    }
}

impl From<&LitFixedVec> for LitVec {
    #[inline]
    fn from(lits: &LitFixedVec) -> Self {
        Self::from(lits.as_slice())
    }
}

impl From<LitFixedVec> for LitVec {
    #[inline]
    fn from(lits: LitFixedVec) -> Self {
        Self::from(lits.as_slice())
    }
}

impl Clone for LitFixedVec {
    #[inline]
    fn clone(&self) -> Self {
        Self::from(self.as_slice())
    }
}

impl Drop for LitFixedVec {
    #[inline]
    fn drop(&mut self) {
        if let Some(data) = self.0 {
            // SAFETY: this owner exclusively owns the malloc allocation; Lit
            // has no destructor and no references outlive this owner.
            unsafe { libc::free(data.as_ptr().cast()) };
        }
    }
}

impl Deref for LitFixedVec {
    type Target = [Lit];

    #[inline]
    fn deref(&self) -> &[Lit] {
        match self.0 {
            // SAFETY: the initialized payload has len elements and remains
            // alive for the lifetime of self.
            Some(data) => unsafe {
                slice::from_raw_parts(data.as_ptr().add(1).cast::<Lit>(), self.len() as usize)
            },
            None => &[],
        }
    }
}

impl DerefMut for LitFixedVec {
    #[inline]
    fn deref_mut(&mut self) -> &mut [Lit] {
        match self.0 {
            // SAFETY: as above, with exclusive access to the allocation.
            Some(data) => unsafe {
                slice::from_raw_parts_mut(data.as_ptr().add(1).cast::<Lit>(), self.len() as usize)
            },
            None => &mut [],
        }
    }
}

impl AsRef<[Lit]> for LitFixedVec {
    #[inline]
    fn as_ref(&self) -> &[Lit] {
        self
    }
}

impl<'a> IntoIterator for &'a LitFixedVec {
    type Item = &'a Lit;
    type IntoIter = slice::Iter<'a, Lit>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl PartialEq for LitFixedVec {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Eq for LitFixedVec {}

impl Not for &LitFixedVec {
    type Output = LitVec;

    #[inline]
    fn not(self) -> LitVec {
        self.map(|lit| !lit)
    }
}

impl std::hash::Hash for LitFixedVec {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(self.as_slice(), state);
    }
}

impl Debug for LitFixedVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl Display for LitFixedVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Serialize for LitFixedVec {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut state = serializer.serialize_struct("LitVec", 1)?;
        state.serialize_field("lits", self.as_slice())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for LitFixedVec {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        LitVec::deserialize(deserializer).map(Self::from)
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub struct LitVec {
    lits: Vec<Lit>,
}

impl LitVec {
    #[inline]
    pub fn new() -> Self {
        LitVec { lits: Vec::new() }
    }

    #[inline]
    pub fn new_with_cap(c: usize) -> Self {
        LitVec {
            lits: Vec::with_capacity(c),
        }
    }

    #[inline]
    pub fn last(&self) -> Lit {
        #[cfg(debug_assertions)]
        {
            self.lits.last().copied().unwrap()
        }
        #[cfg(not(debug_assertions))]
        unsafe {
            self.lits.last().copied().unwrap_unchecked()
        }
    }

    /// Simplify sorted literals in place, reusing the existing buffer.
    /// Returns `None` for a satisfied or tautological clause.
    #[inline]
    pub fn ordered_simp(mut self, v: &VarAssign) -> Option<Self> {
        let len = ordered_simp_in_place(&mut self, v)?;
        self.truncate(len);
        Some(self)
    }

    #[inline]
    pub fn subsume(&self, o: &[Lit]) -> bool {
        if self.len() > o.len() {
            return false;
        }
        'n: for x in self.iter() {
            for y in o.iter() {
                if x == y {
                    continue 'n;
                }
            }
            return false;
        }
        true
    }

    pub fn subsume_execpt_one(&self, o: &[Lit]) -> (bool, Option<Lit>) {
        if self.len() > o.len() {
            return (false, None);
        }
        let mut diff = None;
        'n: for x in self.iter() {
            for y in o.iter() {
                if x == y {
                    continue 'n;
                }
                if diff.is_none() && x.var() == y.var() {
                    diff = Some(*x);
                    continue 'n;
                }
            }
            return (false, None);
        }

        (diff.is_none(), diff)
    }

    #[inline]
    pub fn ordered_subsume(&self, cube: &LitVec) -> bool {
        debug_assert!(self.is_sorted());
        debug_assert!(cube.is_sorted());
        if self.len() > cube.len() {
            return false;
        }
        let mut j = 0;
        for i in 0..self.len() {
            while j < cube.len() && self[i].0 > cube[j].0 {
                j += 1;
            }
            if j == cube.len() || self[i] != cube[j] {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn ordered_subsume_execpt_one(&self, cube: &LitVec) -> (bool, Option<Lit>) {
        ordered_subsume_except_one_slice(self, cube)
    }

    #[inline]
    pub fn intersection(&self, cube: &LitVec) -> LitVec {
        let x_lit_set = self.iter().collect::<GHashSet<&Lit>>();
        let y_lit_set = cube.iter().collect::<GHashSet<&Lit>>();
        Self {
            lits: x_lit_set
                .intersection(&y_lit_set)
                .copied()
                .copied()
                .collect(),
        }
    }

    #[inline]
    pub fn ordered_intersection(&self, cube: &LitVec) -> LitVec {
        debug_assert!(self.is_sorted());
        debug_assert!(cube.is_sorted());
        let mut res = LitVec::new();
        let mut i = 0;
        for l in self.iter() {
            while i < cube.len() && cube[i] < *l {
                i += 1;
            }
            if i == cube.len() {
                break;
            }
            if *l == cube[i] {
                res.push(*l);
            }
        }
        res
    }

    #[inline]
    pub fn resolvent(&self, other: &LitVec, v: Var) -> Option<LitVec> {
        let (x, y) = if self.len() < other.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut new = LitVec::new();
        'n: for x in x.iter() {
            if x.var() != v {
                for y in y.iter() {
                    if x.var() == y.var() {
                        if *x == !*y {
                            return None;
                        } else {
                            continue 'n;
                        }
                    }
                }
                new.push(*x);
            }
        }
        new.extend(y.iter().filter(|l| l.var() != v).copied());
        Some(new)
    }

    /// Remove `v` and merge two sorted clauses into a sorted, duplicate-free
    /// resolvent. Return `None` if the remaining literals are complementary.
    /// The caller checks that the clauses contain opposite pivot literals.
    #[inline]
    pub fn ordered_resolvent(&self, other: &LitVec, v: Var) -> Option<LitVec> {
        ordered_resolvent_slice(self, other, v)
    }

    #[inline]
    pub fn map_var(&self, f: impl Fn(Var) -> Var) -> LitVec {
        let mut new = LitVec::new_with_cap(self.len());
        for l in self.iter() {
            new.push(l.map_var(&f));
        }
        new
    }

    #[inline]
    pub fn filter_map_var(&self, f: impl Fn(Var) -> Option<Var>) -> LitVec {
        let mut new = LitVec::new_with_cap(self.len());
        for l in self.iter() {
            if let Some(l) = l.filter_map_var(&f) {
                new.push(l);
            }
        }
        new
    }

    #[inline]
    pub fn map(&self, f: impl Fn(Lit) -> Lit) -> LitVec {
        let mut new = LitVec::new_with_cap(self.len());
        for l in self.iter() {
            new.push(f(*l));
        }
        new
    }

    #[inline]
    pub fn filter_map(&self, f: impl Fn(Lit) -> Option<Lit>) -> LitVec {
        let mut new = LitVec::new_with_cap(self.len());
        for &l in self.iter() {
            if let Some(l) = f(l) {
                new.push(l);
            }
        }
        new
    }

    #[inline]
    pub fn filter(&self, f: impl Fn(Lit) -> bool) -> LitVec {
        let mut new = LitVec::new_with_cap(self.len());
        for &l in self.iter() {
            if f(l) {
                new.push(l);
            }
        }
        new
    }
}

impl Default for LitVec {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for LitVec {
    type Target = Vec<Lit>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.lits
    }
}

impl DerefMut for LitVec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lits
    }
}

impl PartialOrd for LitVec {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LitVec {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        debug_assert!(self.is_sorted());
        debug_assert!(other.is_sorted());
        let min_index = self.len().min(other.len());
        for i in 0..min_index {
            match self[i].0.cmp(&other[i].0) {
                Ordering::Less => return Ordering::Less,
                Ordering::Equal => {}
                Ordering::Greater => return Ordering::Greater,
            }
        }
        self.len().cmp(&other.len())
    }
}

impl Not for LitVec {
    type Output = LitVec;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        LitVec { lits }
    }
}

impl Not for &LitVec {
    type Output = LitVec;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        LitVec { lits }
    }
}

impl<const N: usize> From<[Lit; N]> for LitVec {
    #[inline]
    fn from(s: [Lit; N]) -> Self {
        Self { lits: Vec::from(s) }
    }
}

impl From<Lit> for LitVec {
    #[inline]
    fn from(l: Lit) -> Self {
        Self { lits: vec![l] }
    }
}

impl From<&[Lit]> for LitVec {
    #[inline]
    fn from(s: &[Lit]) -> Self {
        Self { lits: Vec::from(s) }
    }
}

impl From<&LitVec> for LitVec {
    #[inline]
    fn from(s: &LitVec) -> Self {
        s.clone()
    }
}

impl From<LitVec> for Vec<Lit> {
    #[inline]
    fn from(val: LitVec) -> Self {
        val.lits
    }
}

impl FromIterator<Lit> for LitVec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            lits: Vec::from_iter(iter),
        }
    }
}

impl IntoIterator for LitVec {
    type Item = Lit;
    type IntoIter = std::vec::IntoIter<Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.into_iter()
    }
}

impl<'a> IntoIterator for &'a LitVec {
    type Item = &'a Lit;
    type IntoIter = slice::Iter<'a, Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl AsRef<[Lit]> for LitVec {
    #[inline]
    fn as_ref(&self) -> &[Lit] {
        self.as_slice()
    }
}

impl AsRef<LitVec> for LitVec {
    #[inline]
    fn as_ref(&self) -> &LitVec {
        self
    }
}

impl AsMut<LitVec> for LitVec {
    #[inline]
    fn as_mut(&mut self) -> &mut LitVec {
        self
    }
}

impl Display for LitVec {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.lits.fmt(f)
    }
}

impl Debug for LitVec {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.lits.fmt(f)
    }
}

#[inline]
fn ordered_simp_in_place(lits: &mut [Lit], v: &VarAssign) -> Option<usize> {
    debug_assert!(lits.is_sorted());
    let mut len = 0;
    for i in 0..lits.len() {
        let lit = lits[i];
        let lv = v.v(lit);
        if lv.is_true() {
            return None;
        } else if lv.is_false() {
            continue;
        }
        if len > 0 {
            let last = lits[len - 1];
            if lit == last {
                continue;
            } else if lit == !last {
                return None;
            }
        }
        lits[len] = lit;
        len += 1;
    }
    Some(len)
}

#[inline]
fn ordered_subsume_except_one_slice(lits: &[Lit], cube: &[Lit]) -> (bool, Option<Lit>) {
    debug_assert!(lits.is_sorted());
    debug_assert!(cube.is_sorted());
    let mut diff = None;
    if lits.len() > cube.len() {
        return (false, None);
    }
    let mut j = 0;
    for &lit in lits {
        while j < cube.len() && lit.var() > cube[j].var() {
            j += 1;
        }
        if j == cube.len() {
            return (false, None);
        }
        if lit != cube[j] {
            if diff.is_none() && lit.var() == cube[j].var() {
                diff = Some(lit);
            } else {
                return (false, None);
            }
        }
    }
    (diff.is_none(), diff)
}

#[inline]
fn ordered_resolvent_slice(lits: &[Lit], other: &[Lit], v: Var) -> Option<LitVec> {
    debug_assert!(lits.is_sorted());
    debug_assert!(other.is_sorted());
    let mut new = LitVec::new_with_cap(lits.len() + other.len());
    let (mut i, mut j) = (0, 0);
    while i < lits.len() || j < other.len() {
        let lit = if i < lits.len() && (j == other.len() || lits[i] <= other[j]) {
            let lit = lits[i];
            i += 1;
            lit
        } else {
            let lit = other[j];
            j += 1;
            lit
        };
        if lit.var() == v {
            continue;
        }
        if let Some(&last) = new.lits.last() {
            if lit == last {
                continue;
            }
            if lit == !last {
                return None;
            }
        }
        new.push(lit);
    }
    Some(new)
}
