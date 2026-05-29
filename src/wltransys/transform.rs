use crate::wltransys::{
    cert::{WlCex, WlProof},
    symbol::WlTsSymbol,
};
use giputils::hash::GHashMap;
use logicrs::fol::Term;
use std::mem::take;

pub trait WlTransform {
    fn trans_sym(&self, sym: &mut WlTsSymbol);

    /// Inversely transform word-level counterexample.
    fn inv_trans_cex(&self, cex: &mut WlCex);

    /// Inversely transform word-level proof.
    fn inv_trans_proof(&self, proof: &mut WlProof);
}

pub struct WlTransformStack {
    trans: Vec<Box<dyn WlTransform>>,
}

impl WlTransformStack {
    pub fn new() -> Self {
        Self { trans: Vec::new() }
    }

    pub fn add(&mut self, trans: Box<dyn WlTransform>) {
        self.trans.push(trans);
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

    fn inv_trans_cex(&self, _cex: &mut WlCex) {
        // No action is needed because this map does not affect inputs or latches.
    }

    fn inv_trans_proof(&self, _proof: &mut WlProof) {
        // No action is needed because this map does not affect inputs or latches.
    }
}
