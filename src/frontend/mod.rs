use crate::{
    BlProof, BlWitness,
    frontend::{aig::certifaiger_check, btor::cerbtora_check},
    transys::Transys,
    wltransys::{
        WlTransys,
        certify::{WlProof, WlWitness},
    },
};
use giputils::hash::GHashMap;
use log::{error, info};
use logicrs::{VarSymbols, fol::Term};
use std::{
    fmt::Display,
    path::{Path, PathBuf},
};

pub mod aig;
pub mod btor;

pub trait Frontend {
    fn ts(&mut self) -> (Transys, VarSymbols);

    fn wts(&mut self) -> (WlTransys, GHashMap<Term, String>) {
        panic!("frontend unsupported for wltransys")
    }

    fn safe_certificate(&mut self, proof: BlProof) -> Box<dyn Display>;

    fn unsafe_certificate(&mut self, witness: BlWitness) -> Box<dyn Display>;

    fn wl_safe_certificate(&mut self, _proof: WlProof) -> Box<dyn Display> {
        panic!("frontend unsupported for word level certificate")
    }

    fn wl_unsafe_certificate(&mut self, _witness: WlWitness) -> Box<dyn Display> {
        panic!("frontend unsupported for word level certificate")
    }

    fn certify(&mut self, model: &Path, cert: &Path) -> bool;
}

pub fn certificate_check(model: &PathBuf, certificate: impl AsRef<Path>) -> bool {
    let res = match model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => certifaiger_check(model, certificate),
        Some(ext) if (ext == "btor") | (ext == "btor2") => cerbtora_check(model, certificate),
        _ => {
            unreachable!();
        }
    };
    if res {
        info!("certificate verification passed");
    } else {
        error!("certificate verification failed");
    }
    res
}
