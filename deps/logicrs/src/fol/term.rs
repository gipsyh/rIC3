use super::op::{Add, And, Ite, Neg, Not, Or, Sub, Xor};
use super::{op::FolOp, sort::Sort};
use crate::OptLevel;
use crate::fol::op::{Concat, Slice};
use crate::fol::simplify::SimplifyCtx;
use crate::fol::{OpTrait, TermVec, Value, op, term_mgr};
use giputils::bitvec::BitVec;
use giputils::hash::GHashMap;
use giputils::ptr::Grc;
use serde::{Deserialize, Deserializer, Serialize, Serializer, de};
use std::fmt::{self, Debug};
use std::hash;
use std::iter::once;
use std::ops::Index;
use std::{hash::Hash, ops::Deref};

#[derive(Clone)]
pub struct Term {
    pub(super) inner: Grc<TermInner>,
}

impl Term {
    #[inline]
    pub fn id(&self) -> usize {
        self.inner.id
    }

    #[inline]
    pub fn bool_const(c: bool) -> Term {
        term_mgr().new_term(TermType::Const(BitVec::from(&[c])), Sort::Bv(1))
    }

    #[inline]
    pub fn bv_const(c: BitVec) -> Term {
        let sort = Sort::Bv(c.len());
        term_mgr().new_term(TermType::Const(c), sort)
    }

    #[inline]
    pub fn new_op(op: FolOp, terms: impl IntoIterator<Item = impl AsRef<Term>>) -> Term {
        let mut terms: Vec<Term> = terms.into_iter().map(|t| t.as_ref().clone()).collect();
        debug_assert!(!terms.is_empty());
        if !op.is_core() {
            return op.normalize(&terms);
        }
        if op.traits().contains(OpTrait::Commutative) {
            terms.sort_by_key(|t| t.id());
        }
        if let Some(t) = op.simplify(
            &SimplifyCtx {
                level: OptLevel::O0,
            },
            &terms,
        ) {
            return t;
        }
        let sort = op.sort(&terms);
        let term = TermType::Op(OpTerm::new(op, terms));
        term_mgr().new_term(term, sort)
    }

    #[inline]
    pub fn new_var(sort: Sort) -> Term {
        term_mgr().new_var(sort)
    }

    #[inline]
    pub fn new_op_fold(op: FolOp, terms: impl IntoIterator<Item = impl AsRef<Term>>) -> Term {
        let mut terms = terms.into_iter();
        let acc = terms.next().unwrap().as_ref().clone();
        terms.fold(acc, |acc, x| Self::new_op(op, &[acc, x.as_ref().clone()]))
    }

    /// can only be used for bool terms
    pub fn new_ands(terms: impl IntoIterator<Item = impl AsRef<Term>>) -> Term {
        terms.into_iter().fold(Term::bool_const(true), |acc, x| {
            Self::new_op(op::And, &[acc, x.as_ref().clone()])
        })
    }

    /// can only be used for bool terms
    pub fn new_ors(terms: impl IntoIterator<Item = impl AsRef<Term>>) -> Term {
        terms.into_iter().fold(Term::bool_const(false), |acc, x| {
            Self::new_op(op::Or, &[acc, x.as_ref().clone()])
        })
    }

    #[inline]
    pub fn new_op_elementwise(
        op: FolOp,
        x: impl IntoIterator<Item = impl AsRef<Term>>,
        y: impl IntoIterator<Item = impl AsRef<Term>>,
    ) -> TermVec {
        x.into_iter()
            .zip(y)
            .map(|(x, y)| Self::new_op(op, [x.as_ref(), y.as_ref()]))
            .collect()
    }
}

impl Term {
    #[inline]
    pub fn sort(&self) -> Sort {
        self.inner.sort()
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        self.sort().is_bool()
    }

    #[inline]
    pub fn is_const(&self) -> bool {
        matches!(self.deref(), TermType::Const(_))
    }

    #[inline]
    pub fn is_var(&self) -> bool {
        matches!(self.deref(), TermType::Var(_))
    }

    #[inline]
    pub fn is_op(&self) -> bool {
        matches!(self.deref(), TermType::Op(_))
    }

    #[inline]
    pub fn try_op(&self) -> Option<&OpTerm> {
        if let TermType::Op(op) = self.deref() {
            Some(op)
        } else {
            None
        }
    }

    #[inline]
    pub fn bv_len(&self) -> usize {
        self.sort().bv()
    }

    #[inline]
    pub fn try_bv_const(&self) -> Option<&BitVec> {
        match self.deref() {
            TermType::Const(c) => Some(c),
            _ => None,
        }
    }

    #[inline]
    pub fn try_bool_const(&self) -> Option<bool> {
        match self.deref() {
            TermType::Const(c) => c.try_bool(),
            _ => None,
        }
    }

    #[inline]
    pub fn op<'a>(
        &'a self,
        op: FolOp,
        terms: impl IntoIterator<Item = impl AsRef<Term> + 'a>,
    ) -> Term {
        let terms = once(self.clone()).chain(terms.into_iter().map(|l| l.as_ref().clone()));
        Self::new_op(op, terms)
    }

    #[inline]
    pub fn op0(&self, op: FolOp) -> Term {
        Self::new_op(op, [self])
    }

    #[inline]
    pub fn op1(&self, op: FolOp, x: impl AsRef<Term>) -> Term {
        Self::new_op(op, [self, x.as_ref()])
    }

    #[inline]
    pub fn op2(&self, op: FolOp, x: impl AsRef<Term>, y: impl AsRef<Term>) -> Term {
        Self::new_op(op, [self, x.as_ref(), y.as_ref()])
    }

    #[inline]
    pub fn imply(&self, x: impl AsRef<Term>) -> Term {
        self.op1(op::Implies, x)
    }

    #[inline]
    pub fn not_if(&self, c: bool) -> Term {
        if c { !self } else { self.clone() }
    }

    #[inline]
    pub fn ite(&self, t: impl AsRef<Term>, e: impl AsRef<Term>) -> Term {
        self.op2(Ite, t, e)
    }

    #[inline]
    pub fn slice(&self, l: usize, h: usize) -> Term {
        let h = Self::bv_const(BitVec::zero(h));
        let l = Self::bv_const(BitVec::zero(l));
        self.op2(Slice, &h, &l)
    }

    #[inline]
    pub fn sign_bit(&self) -> Term {
        self.slice(self.bv_len() - 1, self.bv_len() - 1)
    }

    #[inline]
    pub fn concat(&self, o: impl AsRef<Term>) -> Term {
        self.op1(Concat, o)
    }

    /// Term Eq, different from PartialEq trait
    #[inline]
    pub fn teq(&self, o: impl AsRef<Term>) -> Term {
        self.op1(op::Eq, o)
    }

    /// Term Neq, different from PartialEq trait
    #[inline]
    pub fn tneq(&self, o: impl AsRef<Term>) -> Term {
        self.op1(op::Neq, o)
    }

    #[inline]
    pub fn mk_bv_const_zero(&self) -> Term {
        Term::bv_const(BitVec::zero(self.bv_len()))
    }

    #[inline]
    pub fn mk_bv_const_one(&self) -> Term {
        Term::bv_const(BitVec::one(self.bv_len()))
    }

    #[inline]
    pub fn mk_bv_const_ones(&self) -> Term {
        Term::bv_const(BitVec::ones(self.bv_len()))
    }

    #[inline]
    pub fn cached_apply(
        &self,
        r: &impl Fn(&Term) -> Option<Term>,
        map: &mut GHashMap<Term, Term>,
    ) -> Term {
        if let Some(r) = map.get(self) {
            return r.clone();
        }
        let r = if let Some(r) = r(self) {
            r
        } else {
            self.try_op()
                .map(|op_term| {
                    let a: Vec<Term> = op_term
                        .terms
                        .iter()
                        .map(|t| t.cached_apply(r, map))
                        .collect();
                    Term::new_op(op_term.op, a)
                })
                .unwrap_or(self.clone())
        };
        map.insert(self.clone(), r.clone());
        r
    }

    pub fn apply(&self, r: &impl Fn(&Term) -> Option<Term>) -> Term {
        self.cached_apply(&r, &mut GHashMap::new())
    }

    pub fn simulate(&self, val: &mut GHashMap<Term, Value>) -> Value {
        if let Some(v) = val.get(self) {
            return v.clone();
        }
        let v = match self.deref() {
            TermType::Const(c) => Value::Bv(c.clone().into()),
            TermType::Var(_) => Value::default_from(self.sort()),
            TermType::Op(op_term) => {
                let child_vals: Vec<Value> =
                    op_term.terms.iter().map(|t| t.simulate(val)).collect();
                op_term.op.simulate(&child_vals)
            }
        };
        val.insert(self.clone(), v.clone());
        v
    }
}

impl Deref for Term {
    type Target = TermType;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner.ty
    }
}

impl Hash for Term {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

impl Debug for Term {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.deref().fmt(f)
    }
}

impl Serialize for Term {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.id().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Term {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let id = usize::deserialize(deserializer)?;
        term_mgr()
            .get_term_by_id(id)
            .ok_or_else(|| de::Error::custom(format!("unknown term id {id}")))
    }
}

impl<T: AsRef<Term>> PartialEq<T> for Term {
    #[inline]
    fn eq(&self, other: &T) -> bool {
        let other = other.as_ref();
        self.inner == other.inner
    }
}

impl PartialEq<Term> for &Term {
    #[inline]
    fn eq(&self, other: &Term) -> bool {
        self.inner == other.inner
    }
}

impl std::cmp::Eq for Term {}

impl AsRef<Term> for Term {
    #[inline]
    fn as_ref(&self) -> &Term {
        self
    }
}

impl Drop for Term {
    #[inline]
    fn drop(&mut self) {
        // let g = self.clone();
        // tm().tgc.collect(g);
    }
}

macro_rules! impl_unary_ops {
    ($trait:ident, $method:ident, $op:expr) => {
        impl std::ops::$trait for Term {
            type Output = Term;

            #[inline]
            fn $method(self) -> Self::Output {
                self.op0($op)
            }
        }

        impl std::ops::$trait for &Term {
            type Output = Term;

            #[inline]
            fn $method(self) -> Self::Output {
                self.op0($op)
            }
        }

        impl std::ops::$trait for &mut Term {
            type Output = Term;

            #[inline]
            fn $method(self) -> Self::Output {
                self.op0($op)
            }
        }
    };
}

impl_unary_ops!(Not, not, Not);
impl_unary_ops!(Neg, neg, Neg);

macro_rules! impl_biops {
    ($trait:ident, $method:ident, $op:expr) => {
        impl<T: AsRef<Term>> std::ops::$trait<T> for Term {
            type Output = Term;

            #[inline]
            fn $method(self, rhs: T) -> Self::Output {
                self.op1($op, rhs.as_ref())
            }
        }

        impl<T: AsRef<Term>> std::ops::$trait<T> for &Term {
            type Output = Term;

            #[inline]
            fn $method(self, rhs: T) -> Self::Output {
                self.op1($op, rhs.as_ref())
            }
        }

        impl<T: AsRef<Term>> std::ops::$trait<T> for &mut Term {
            type Output = Term;

            #[inline]
            fn $method(self, rhs: T) -> Self::Output {
                self.op1($op, rhs.as_ref())
            }
        }
    };
}

impl_biops!(BitAnd, bitand, And);
impl_biops!(BitOr, bitor, Or);
impl_biops!(BitXor, bitxor, Xor);
impl_biops!(Add, add, Add);
impl_biops!(Sub, sub, Sub);

pub(super) struct TermInner {
    pub(super) id: usize,
    pub(super) sort: Sort,
    pub(super) ty: TermType,
}

impl TermInner {
    #[inline]
    pub fn sort(&self) -> Sort {
        self.sort
    }
}

impl Debug for TermInner {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ty {
            TermType::Const(c) => c.fmt(f),
            TermType::Var(v) => write!(f, "Var{}, {:?}", *v, self.sort),
            TermType::Op(o) => o.fmt(f),
        }
    }
}

impl Deref for TermInner {
    type Target = TermType;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.ty
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TermType {
    Const(BitVec),
    Var(usize),
    Op(OpTerm),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct OpTerm {
    pub op: FolOp,
    pub terms: Vec<Term>,
}

impl OpTerm {
    #[inline]
    fn new(op: FolOp, terms: Vec<Term>) -> Self {
        Self {
            op,
            terms: terms.to_vec(),
        }
    }
}

impl Debug for OpTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.op.fmt(f)?;
        self.terms.fmt(f)
    }
}

impl Index<usize> for OpTerm {
    type Output = Term;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.terms[index]
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, Default)]
pub struct TermSymbol {
    t2s: GHashMap<Term, Vec<String>>,
    s2t: GHashMap<String, Term>,
}

impl TermSymbol {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn add_symbol(&mut self, t: &Term, s: impl AsRef<str>) {
        let s = s.as_ref().to_string();
        if let Some(existing) = self.s2t.insert(s.clone(), t.clone()) {
            if existing == t {
                return;
            }
            panic!("duplicate signal symbol `{s}`");
        }
        self.t2s.entry(t.clone()).or_default().push(s);
    }

    #[inline]
    pub fn term_of_sym(&self, s: impl AsRef<str>) -> Option<Term> {
        self.s2t.get(s.as_ref()).cloned()
    }

    pub fn remove(&mut self, t: &Term) -> Option<Vec<String>> {
        let r = self.t2s.remove(t);
        if let Some(r) = r.as_ref() {
            for r in r.iter() {
                assert!(self.s2t.remove(r).is_some());
            }
        }
        r
    }

    pub fn remove_sym(&mut self, s: impl AsRef<str>) -> Option<Term> {
        let s = s.as_ref();
        let t = self.s2t.remove(s)?;
        let symbols = self.t2s.get_mut(&t).unwrap();
        symbols.retain(|sym| sym != s);
        if symbols.is_empty() {
            self.t2s.remove(&t);
        }
        Some(t)
    }

    pub fn retain(&mut self, mut f: impl FnMut(&Term) -> bool) {
        self.t2s.retain(|t, _| f(t));
        self.s2t.retain(|_, t| self.t2s.contains_key(t));
    }

    pub fn replace_sym(&mut self, old: impl AsRef<str>, new: impl AsRef<str>) -> bool {
        let old = old.as_ref();
        let new = new.as_ref();
        let Some(t) = self.remove_sym(old) else {
            return false;
        };
        self.add_symbol(&t, new);
        true
    }

    pub fn symbols(&self) -> impl Iterator<Item = &String> {
        self.s2t.keys()
    }
}

impl IntoIterator for TermSymbol {
    type Item = (Term, Vec<String>);
    type IntoIter = <GHashMap<Term, Vec<String>> as IntoIterator>::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.t2s.into_iter()
    }
}

impl Deref for TermSymbol {
    type Target = GHashMap<Term, Vec<String>>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.t2s
    }
}
