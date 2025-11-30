use crate::{
    Proof, Witness,
    transys::Transys,
    wltransys::{
        WlTransys,
        certify::{WlProof, WlWitness},
    },
};
use giputils::hash::GHashMap;
use logicrs::{VarSymbols, fol::Term};
use std::{fmt::Display, path::Path};

pub mod aig;
pub mod btor;

pub trait Frontend {
    fn ts(&mut self) -> (Transys, VarSymbols);

    fn wts(&mut self) -> (WlTransys, GHashMap<Term, String>) {
        panic!("frontend unsupported for wltransys")
    }

    fn safe_certificate(&mut self, proof: Proof) -> Box<dyn Display>;

    fn unsafe_certificate(&mut self, witness: Witness) -> Box<dyn Display>;

    fn wl_safe_certificate(&mut self, _proof: WlProof) -> Box<dyn Display> {
        panic!("frontend unsupported for word level certificate")
    }

    fn wl_unsafe_certificate(&mut self, _witness: WlWitness) -> Box<dyn Display> {
        panic!("frontend unsupported for word level certificate")
    }

    fn certify(&mut self, model: &Path, cert: &Path) -> bool;
}
