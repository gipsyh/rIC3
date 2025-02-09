use super::IC3;
use giputils::grc::Grc;
use logic_form::{Lemma, LitVec};
use std::cmp::Ordering;
use std::collections::{btree_set, BTreeSet};
use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};

#[derive(Default)]
pub struct ProofObligationInner {
    pub frame: usize,
    pub input: LitVec,
    pub lemma: Lemma,
    pub depth: usize,
    pub next: Option<ProofObligation>,
    pub removed: bool,
    pub act: f64,
}

impl PartialEq for ProofObligationInner {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.lemma == other.lemma && self.removed == other.removed
    }
}

impl Eq for ProofObligationInner {}

impl PartialOrd for ProofObligationInner {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ProofObligationInner {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match other.frame.cmp(&self.frame) {
            Ordering::Equal => match self.depth.cmp(&other.depth) {
                Ordering::Equal => match other.lemma.len().cmp(&self.lemma.len()) {
                    Ordering::Equal => match other.lemma.cmp(&self.lemma) {
                        Ordering::Equal => self.removed.cmp(&other.removed),
                        ord => ord,
                    },
                    ord => ord,
                },
                ord => ord,
            },
            ord => ord,
        }
    }
}

impl Debug for ProofObligationInner {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProofObligation")
            .field("frame", &self.frame)
            .field("lemma", &self.lemma)
            .field("depth", &self.depth)
            .finish()
    }
}

#[derive(Clone, Default)]
pub struct ProofObligation {
    inner: Grc<ProofObligationInner>,
}

impl ProofObligation {
    pub fn new(
        frame: usize,
        lemma: Lemma,
        input: LitVec,
        depth: usize,
        next: Option<Self>,
    ) -> Self {
        Self {
            inner: Grc::new(ProofObligationInner {
                frame,
                input,
                lemma,
                depth,
                next,
                removed: false,
                act: 0.0,
            }),
        }
    }

    pub fn bump_act(&mut self) {
        self.act += 1.0;
    }

    pub fn push_to(&mut self, frame: usize) {
        for _ in self.frame..frame {
            self.act *= 0.6;
        }
        self.frame = frame;
    }

    #[inline]
    pub fn set(&mut self, other: &ProofObligation) {
        self.inner = other.inner.clone();
    }
}

impl Deref for ProofObligation {
    type Target = ProofObligationInner;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for ProofObligation {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl PartialEq for ProofObligation {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl Eq for ProofObligation {}

impl PartialOrd for ProofObligation {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ProofObligation {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl Debug for ProofObligation {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[derive(Default, Debug)]
pub struct ProofObligationQueue {
    obligations: BTreeSet<ProofObligation>,
    num: Vec<usize>,
}

impl ProofObligationQueue {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, po: ProofObligation) {
        if self.num.len() <= po.frame {
            self.num.resize(po.frame + 1, 0);
        }
        self.num[po.frame] += 1;
        assert!(self.obligations.insert(po));
    }

    pub fn pop(&mut self, depth: usize) -> Option<ProofObligation> {
        if let Some(po) = self.obligations.last().filter(|po| po.frame <= depth) {
            self.num[po.frame] -= 1;
            self.obligations.pop_last()
        } else {
            None
        }
    }

    pub fn peak(&mut self) -> Option<ProofObligation> {
        self.obligations.last().cloned()
    }

    pub fn remove(&mut self, po: &ProofObligation) -> bool {
        let ret = self.obligations.remove(po);
        if ret {
            self.num[po.frame] -= 1;
        }
        ret
    }

    pub fn clear(&mut self) {
        self.obligations.clear();
        for n in self.num.iter_mut() {
            *n = 0;
        }
    }

    #[allow(unused)]
    pub fn iter(&self) -> btree_set::Iter<'_, ProofObligation> {
        self.obligations.iter()
    }

    pub fn statistic(&self) {
        println!("{:?}", self.num);
    }
}

impl IC3 {
    pub fn add_obligation(&mut self, po: ProofObligation) {
        self.statistic.avg_po_cube_len += po.lemma.len();
        self.obligations.add(po)
    }

    pub fn witness(&mut self) -> Vec<ProofObligation> {
        let mut witness = Vec::new();
        let mut bad = self.obligations.pop(0).unwrap();
        witness.push(bad.clone());
        while bad.next.is_some() {
            bad = bad.next.clone().unwrap();
            witness.push(bad.clone());
        }
        witness
    }
}
