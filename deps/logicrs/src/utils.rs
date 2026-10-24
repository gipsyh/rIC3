use crate::{LboolVec, Lit, Var, VarRange};
use giputils::hash::GHashMap;
use serde::{Deserialize, Serialize};
use std::{
    fmt::{self, Debug, Display},
    mem::take,
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr, slice,
};

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct VarMap<T> {
    map: Vec<T>,
}

impl<T: Default> VarMap<T> {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn new_with(var: Var) -> Self {
        let mut res = Self::new();
        res.reserve(var);
        res
    }

    #[inline]
    pub fn max_var(&self) -> Var {
        assert!(!self.is_empty());
        Var((self.len() as u32) - 1)
    }

    #[inline]
    pub fn reserve(&mut self, var: Var) {
        let len = Into::<usize>::into(var) + 1;
        if self.len() < len {
            self.map.resize_with(len, Default::default)
        }
    }

    #[inline]
    pub fn swap(&mut self, x: Var, y: Var) {
        let px = ptr::addr_of_mut!(self[x]);
        let py = ptr::addr_of_mut!(self[y]);
        unsafe {
            ptr::swap(px, py);
        }
    }
}

impl<T, I> Index<I> for VarMap<T>
where
    I: Into<Var>,
{
    type Output = T;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        let index = index.into();

        #[cfg(not(debug_assertions))]
        unsafe {
            self.map.get_unchecked(index.0 as usize)
        }
        #[cfg(debug_assertions)]
        &self.map[index.0 as usize]
    }
}

impl<T, I> IndexMut<I> for VarMap<T>
where
    I: Into<Var>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        let index = index.into();

        #[cfg(not(debug_assertions))]
        unsafe {
            self.map.get_unchecked_mut(index.0 as usize)
        }
        #[cfg(debug_assertions)]
        &mut self.map[index.0 as usize]
    }
}

impl<T> Deref for VarMap<T> {
    type Target = Vec<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl<T> DerefMut for VarMap<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

#[derive(Debug, Default, Clone)]
pub struct LitMap<T> {
    map: Vec<T>,
}

impl<T> LitMap<T> {
    #[inline]
    pub fn new() -> Self {
        Self { map: Vec::new() }
    }
}

impl<T: Default> LitMap<T> {
    #[inline]
    pub fn new_with(var: Var) -> Self {
        let mut res = Self::new();
        res.reserve(var);
        res
    }

    #[inline]
    pub fn reserve(&mut self, var: Var) {
        let len = (Into::<usize>::into(var) + 1) * 2;
        if self.len() < len {
            self.map.resize_with(len, Default::default)
        }
    }

    #[inline]
    pub fn max_index(&self) -> Var {
        Var((self.len() as u32 / 2) - 1)
    }

    #[inline]
    pub fn swap(&mut self, x: Lit, y: Lit) {
        let px = ptr::addr_of_mut!(self[x]);
        let py = ptr::addr_of_mut!(self[y]);
        unsafe {
            ptr::swap(px, py);
        }
    }
}

impl<T> Index<Lit> for LitMap<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: Lit) -> &Self::Output {
        #[cfg(not(debug_assertions))]
        unsafe {
            self.map.get_unchecked(index.0 as usize)
        }
        #[cfg(debug_assertions)]
        &self.map[index.0 as usize]
    }
}

impl<T> IndexMut<Lit> for LitMap<T> {
    #[inline]
    fn index_mut(&mut self, index: Lit) -> &mut Self::Output {
        #[cfg(not(debug_assertions))]
        unsafe {
            self.map.get_unchecked_mut(index.0 as usize)
        }
        #[cfg(debug_assertions)]
        &mut self.map[index.0 as usize]
    }
}

impl<T> Deref for LitMap<T> {
    type Target = Vec<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl<T> DerefMut for LitMap<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

#[derive(Default, Clone)]
pub struct VarSet {
    pub set: Vec<Var>,
    pub has: VarMap<bool>,
}

impl VarSet {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn new_with(var: Var) -> Self {
        let mut res = Self::new();
        res.reserve(var);
        res
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> u32 {
        self.set.len() as _
    }

    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.has.reserve(var);
    }

    #[inline]
    pub fn has(&self, var: Var) -> bool {
        self.has[var]
    }

    #[inline]
    pub fn insert(&mut self, var: Var) {
        if !self.has[var] {
            self.set.push(var);
            self.has[var] = true;
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        for l in self.set.iter() {
            self.has[*l] = false;
        }
        self.set.clear();
    }

    #[inline]
    pub fn iter(&'_ self) -> slice::Iter<'_, Var> {
        self.set.iter()
    }

    #[inline]
    pub fn remove(&mut self, i: u32) {
        let v = self.set.swap_remove(i as usize);
        self.has[v] = false;
    }

    #[inline]
    pub fn swap(&mut self, a: u32, b: u32) {
        self.set.swap(a as usize, b as usize)
    }

    #[inline]
    pub fn elements(&self) -> &[Var] {
        &self.set
    }
}

impl Index<u32> for VarSet {
    type Output = Var;

    #[inline]
    fn index(&self, index: u32) -> &Self::Output {
        &self.set[index as usize]
    }
}

#[derive(Default, Debug, Clone)]
pub struct LitSet {
    set: Vec<Lit>,
    has: LitMap<bool>,
}

impl LitSet {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn new_with(var: Var) -> Self {
        let mut res = Self::new();
        res.reserve(var);
        res
    }

    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.has.reserve(var);
    }

    #[inline]
    pub fn insert(&mut self, lit: Lit) {
        if !self.has[lit] {
            self.set.push(lit);
            self.has[lit] = true;
        }
    }

    #[inline]
    pub fn has(&self, lit: Lit) -> bool {
        self.has[lit]
    }

    #[inline]
    pub fn clear(&mut self) {
        for l in self.set.iter() {
            self.has[*l] = false;
        }
        self.set.clear();
    }

    #[inline]
    pub fn iter(&'_ self) -> slice::Iter<'_, Lit> {
        self.set.iter()
    }

    #[inline]
    pub fn elements(&self) -> &[Lit] {
        &self.set
    }
}

#[derive(Default)]
pub struct VarRef {
    set: Vec<Var>,
    refs: VarMap<u32>,
    dirty: VarMap<bool>,
}

impl VarRef {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.refs.reserve(var);
        self.dirty.reserve(var);
    }

    #[inline]
    pub fn inref(&mut self, var: Var) {
        self.refs[var] += 1;
        if self.refs[var] == 1 {
            if self.dirty[var] {
                self.dirty[var] = false
            } else {
                self.set.push(var)
            }
        }
    }

    #[inline]
    pub fn deref(&mut self, var: Var) {
        assert!(self.refs[var] > 0);
        self.refs[var] -= 1;
        if self.refs[var] == 0 {
            self.dirty[var] = true;
        }
    }

    #[inline]
    pub fn iter(&self) -> VarRefIter {
        VarRefIter {
            varref: self as *const VarRef as *mut VarRef,
            p: 0,
        }
    }
}

pub struct VarRefIter {
    varref: *mut VarRef,
    p: usize,
}

impl Iterator for VarRefIter {
    type Item = Var;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let varref = unsafe { &mut *self.varref };
        while self.p < varref.set.len() && varref.dirty[varref.set[self.p]] {
            varref.dirty[varref.set[self.p]] = false;
            varref.set.swap_remove(self.p);
        }
        if self.p >= varref.set.len() {
            return None;
        }
        self.p += 1;
        Some(varref.set[self.p - 1])
    }
}

#[derive(Clone, Debug, Default)]
pub struct VarVMap {
    map: GHashMap<Var, Var>,
}

impl Deref for VarVMap {
    type Target = GHashMap<Var, Var>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl DerefMut for VarVMap {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

impl Index<Var> for VarVMap {
    type Output = Var;

    #[inline]
    fn index(&self, index: Var) -> &Self::Output {
        &self.map[&index]
    }
}

impl VarVMap {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn new_self_map(v: Var) -> Self {
        let mut res = VarVMap::new();
        for v in VarRange::new_inclusive(Var::CONST, v) {
            res.insert(v, v);
        }
        res
    }

    #[inline]
    pub fn lit_map(&self, lit: Lit) -> Option<Lit> {
        self.map
            .get(&lit.var())
            .map(|v| v.lit().not_if(!lit.polarity()))
    }

    pub fn product(&self, other: &Self) -> Self {
        let mut res = VarVMap::new();
        for (x, y) in self.iter() {
            if let Some(z) = other.get(y) {
                res.insert(*x, *z);
            }
        }
        res
    }

    pub fn inverse(&self) -> Self {
        let mut res = VarVMap::new();
        for (x, y) in self.iter() {
            res.insert(*y, *x);
        }
        res
    }

    pub fn map_fn(&self) -> impl Fn(Var) -> Var + '_ {
        move |v| self[v]
    }

    pub fn try_map_fn(&self) -> impl Fn(Var) -> Option<Var> + '_ {
        move |v| self.get(&v).copied()
    }

    pub fn map_key(&mut self, map: impl Fn(Var) -> Var) {
        for (k, v) in take(&mut self.map) {
            self.insert(map(k), v);
        }
    }

    pub fn map_value(&mut self, map: impl Fn(Var) -> Var) {
        for (k, v) in take(&mut self.map) {
            self.insert(k, map(v));
        }
    }

    pub fn filter_map_key(&mut self, map: impl Fn(Var) -> Option<Var>) {
        for (k, v) in take(&mut self.map) {
            if let Some(n) = map(k) {
                self.insert(n, v);
            }
        }
    }

    pub fn filter_map_value(&mut self, map: impl Fn(Var) -> Option<Var>) {
        for (k, v) in take(&mut self.map) {
            if let Some(n) = map(v) {
                self.insert(k, n);
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct VarLMap {
    map: GHashMap<Var, Lit>,
}

impl Deref for VarLMap {
    type Target = GHashMap<Var, Lit>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl DerefMut for VarLMap {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

impl VarLMap {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn insert_lit(&mut self, f: Lit, t: Lit) {
        self.map.insert(f.var(), t.not_if(!f.polarity()));
    }

    #[inline]
    pub fn map(&self, var: Var) -> Option<Lit> {
        self.map.get(&var).copied()
    }

    #[inline]
    pub fn map_lit(&self, lit: Lit) -> Option<Lit> {
        self.map.get(&lit.var()).map(|v| v.not_if(!lit.polarity()))
    }

    pub fn map_fn(&self) -> impl Fn(Lit) -> Lit {
        move |v| self.map_lit(v).unwrap()
    }

    pub fn try_map_fn(&self) -> impl Fn(Lit) -> Option<Lit> {
        move |v| self.map_lit(v)
    }
}

#[derive(Debug, Default, Clone)]
pub struct VarSymbols {
    v2s: GHashMap<Var, Vec<(String, usize)>>,
    s2v: GHashMap<(String, usize), Var>,
}

#[derive(Clone)]
pub struct SymbolAssign {
    pub symbol: String,
    pub assign: LboolVec,
}

impl Debug for SymbolAssign {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.symbol, self.assign)
    }
}

impl Display for SymbolAssign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl VarSymbols {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn insert(&mut self, v: Var, s: String, idx: usize) {
        assert!(self.s2v.insert((s.clone(), idx), v).is_none());
        self.v2s.entry(v).or_default().push((s.clone(), idx));
    }

    #[inline]
    pub fn get(&self, v: Var) -> Vec<(String, usize)> {
        self.v2s.get(&v).cloned().unwrap_or_default()
    }

    pub fn map_var(&self, m: impl Fn(Var) -> Option<Var>) -> Self {
        let mut res = Self::new();
        for (&k, symbols) in self.v2s.iter() {
            for (s, idx) in symbols {
                if let Some(k) = m(k) {
                    res.insert(k, s.clone(), *idx);
                }
            }
        }
        res
    }
}

/// Compiler-style optimization level used by simplification/canonicalization.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OptLevel {
    O0 = 0,
    O1 = 1,
    O2 = 2,
    O3 = 3,
}

impl Default for OptLevel {
    #[inline]
    fn default() -> Self {
        Self::O2
    }
}

impl OptLevel {
    #[inline]
    pub const fn at_least(self, other: OptLevel) -> bool {
        self as u8 >= other as u8
    }
}
