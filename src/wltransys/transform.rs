use crate::wltransys::{
    cert::{WlCex, WlProof},
    symbol::WlTsSymbol,
};
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::Term;
use std::mem::take;

pub trait WlTransform {
    fn trans_sym(&self, _sym: &mut WlTsSymbol) {}

    /// Inversely transform word-level counterexample.
    fn inv_trans_cex(&self, _cex: &mut WlCex) {}

    /// Inversely transform word-level proof.
    fn inv_trans_proof(&self, _proof: &mut WlProof) {}
}

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
                let entry = sym.signal.entry(t.clone()).or_default();
                entry.extend(v);
            }
        }
    }

    // No action is needed for inv cert because this map does not affect inputs or latches.
}

/// External term map transform.
/// Ensure that no other term in the transition system depends on the mapped term.
pub struct WlExtTermMapTf {
    map: GHashMap<Term, Term>,
}

impl WlExtTermMapTf {
    pub fn new(map: GHashMap<Term, Term>) -> Self {
        Self { map }
    }
}

impl WlTransform for WlExtTermMapTf {
    fn trans_sym(&self, sym: &mut WlTsSymbol) {
        for (k, v) in self.map.iter() {
            if let Some(s) = sym.remove(k) {
                let ns = sym.entry(v.clone()).or_default();
                ns.extend(s);
            }
        }
    }

    fn inv_trans_cex(&self, _cex: &mut WlCex) {
        todo!();
    }

    fn inv_trans_proof(&self, _proof: &mut WlProof) {
        todo!()
    }
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
        sym.signal.retain(|term, _| !self.removed.contains(term));
    }

    // No action is needed for inv cert because the removed terms are irrelevant to the property.
}
