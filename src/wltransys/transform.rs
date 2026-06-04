use crate::wltransys::{
    cert::{WlCex, WlProof},
    symbol::WlTsSymbol,
};
use giputils::hash::{GHashMap, GHashSet};
use logicrs::{
    LboolVec,
    fol::{BvTermValue, Term},
};
use std::{mem::take, vec::IntoIter};

pub trait WlTransform: Send {
    fn trans_sym(&self, _sym: &mut WlTsSymbol) {}

    /// Inversely transform word-level counterexample.
    fn inv_trans_cex(&self, _cex: &mut WlCex) {}

    /// Inversely transform word-level proof.
    fn inv_trans_proof(&self, _proof: &mut WlProof) {}
}

#[derive(Default)]
pub struct WlTransformStack {
    trans: Vec<Box<dyn WlTransform>>,
}

impl WlTransformStack {
    pub fn new() -> Self {
        Self { trans: Vec::new() }
    }

    pub fn add(&mut self, trans: impl WlTransform + 'static) {
        self.trans.push(Box::new(trans));
    }

    pub fn extend<I: IntoIterator<Item = Box<dyn WlTransform>>>(&mut self, iter: I) {
        self.trans.extend(iter);
    }
}

impl IntoIterator for WlTransformStack {
    type Item = Box<dyn WlTransform>;

    type IntoIter = IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.trans.into_iter()
    }
}

impl WlTransform for WlTransformStack {
    fn trans_sym(&self, sym: &mut WlTsSymbol) {
        for trans in self.trans.iter() {
            trans.trans_sym(sym);
        }
    }

    fn inv_trans_cex(&self, cex: &mut WlCex) {
        for trans in self.trans.iter().rev() {
            trans.inv_trans_cex(cex);
        }
    }

    fn inv_trans_proof(&self, proof: &mut WlProof) {
        for trans in self.trans.iter().rev() {
            trans.inv_trans_proof(proof);
        }
    }
}

// Internal Term Map Transform
pub struct WlInnTermMapTf {
    map: GHashMap<Term, Term>,
}

impl WlInnTermMapTf {
    pub fn new(map: GHashMap<Term, Term>) -> Self {
        Self { map }
    }
}

impl WlTransform for WlInnTermMapTf {
    fn trans_sym(&self, sym: &mut WlTsSymbol) {
        for (k, v) in take(&mut sym.signal) {
            if let Some(t) = self.map.get(&k) {
                for v in v {
                    sym.add_symbol(&t, v);
                }
            }
        }
    }

    // No action is needed for inv cert because this map does not affect inputs or latches.
}

/// External term merge transform.
/// Ensure that no other term in the transition system depends on the mapped term.
pub struct WlExtTermMergeTf {
    map: GHashMap<Term, Term>,
}

impl WlExtTermMergeTf {
    pub fn new(map: GHashMap<Term, Term>) -> Self {
        Self { map }
    }
}

impl WlTransform for WlExtTermMergeTf {
    fn trans_sym(&self, sym: &mut WlTsSymbol) {
        for (k, v) in self.map.iter() {
            if let Some(s) = sym.remove(k) {
                for s in s {
                    sym.add_symbol(v, s);
                }
            }
        }
    }

    fn inv_trans_cex(&self, cex: &mut WlCex) {
        for input in cex.input.iter_mut() {
            for (k, v) in self.map.iter() {
                let v = v.try_bv_const().unwrap();
                let v = LboolVec::from(v.clone());
                input.push(BvTermValue::new(k.clone(), v));
            }
        }
    }

    fn inv_trans_proof(&self, _proof: &mut WlProof) {}
}

pub struct WlRemoveTf {
    removed: GHashSet<Term>,
}

impl WlRemoveTf {
    pub fn new(removed: GHashSet<Term>) -> Self {
        Self { removed }
    }
}

impl WlTransform for WlRemoveTf {
    fn trans_sym(&self, sym: &mut WlTsSymbol) {
        sym.retain(|term| !self.removed.contains(term));
    }

    // No action is needed for inv cert because the removed terms are irrelevant to the property.
}

pub struct WlKeepTf {
    keep: GHashSet<Term>,
}

impl WlKeepTf {
    pub fn new(keep: GHashSet<Term>) -> Self {
        Self { keep }
    }
}

impl WlTransform for WlKeepTf {
    fn trans_sym(&self, sym: &mut WlTsSymbol) {
        sym.retain(|term| self.keep.contains(term));
    }

    // No action is needed for inv cert because the removed terms are irrelevant to the property.
}
