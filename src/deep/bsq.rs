use logic_form::{Cube, Lemma};
use std::cmp::Ordering;
use std::collections::{btree_set, BTreeSet};
use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

#[derive(Default)]
pub struct BadStateInner {
    pub input: Cube,
    pub lemma: Lemma,
    pub depth: usize,
    pub next: Option<BadState>,
    pub removed: bool,
}

impl PartialEq for BadStateInner {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.lemma == other.lemma && self.removed == other.removed
    }
}

impl Eq for BadStateInner {}

impl PartialOrd for BadStateInner {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BadStateInner {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.depth.cmp(&other.depth) {
            Ordering::Equal => match other.lemma.len().cmp(&self.lemma.len()) {
                Ordering::Equal => match other.lemma.cmp(&self.lemma) {
                    Ordering::Equal => self.removed.cmp(&other.removed),
                    ord => ord,
                },
                ord => ord,
            },
            ord => ord,
        }
    }
}

impl Debug for BadStateInner {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProofObligation")
            .field("lemma", &self.lemma)
            .field("depth", &self.depth)
            .finish()
    }
}

#[derive(Clone, Default)]
pub struct BadState {
    inner: Rc<BadStateInner>,
}

impl BadState {
    pub fn new(lemma: Lemma, input: Cube, depth: usize, next: Option<Self>) -> Self {
        Self {
            inner: Rc::new(BadStateInner {
                input,
                lemma,
                depth,
                next,
                removed: false,
            }),
        }
    }

    #[inline]
    pub fn set(&mut self, other: &BadState) {
        self.inner = other.inner.clone();
    }
}

impl Deref for BadState {
    type Target = BadStateInner;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for BadState {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { Rc::get_mut_unchecked(&mut self.inner) }
    }
}

impl PartialEq for BadState {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl Eq for BadState {}

impl PartialOrd for BadState {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BadState {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl Debug for BadState {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[derive(Default, Debug)]
pub struct BadStateQueue {
    obligations: BTreeSet<BadState>,
    num: Vec<usize>,
}

impl BadStateQueue {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, po: BadState) {
        if self.num.len() <= po.depth {
            self.num.resize(po.depth + 1, 0);
        }
        self.num[po.depth] += 1;
        assert!(self.obligations.insert(po));
    }

    pub fn peak(&mut self) -> Option<BadState> {
        self.obligations.last().cloned()
    }

    pub fn pop(&mut self) -> Option<BadState> {
        match self.obligations.pop_last() {
            Some(b) => {
                self.num[b.depth] -= 1;
                Some(b)
            }
            None => None,
        }
    }

    #[allow(unused)]
    pub fn iter(&self) -> btree_set::Iter<'_, BadState> {
        self.obligations.iter()
    }

    pub fn statistic(&self) {
        println!("{:?}", self.num);
    }
}
