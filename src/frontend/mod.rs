use crate::{
    McProof, McWitness,
    frontend::{
        aig::{AigFrontend, certifaiger_check},
        btor::{BtorFrontend, cerbtora_check},
    },
    transys::Transys,
    wltransys::{WlTransys, symbol::WlTsSymbol},
};
use ::aig::Aig;
use ::btor::Btor;
use anyhow::bail;
use log::{error, info};
use logicrs::VarSymbols;
use std::{
    fmt::Display,
    path::{Path, PathBuf},
};

pub mod aig;
pub mod btor;

pub trait Frontend {
    fn ts(&mut self) -> (Transys, VarSymbols);

    fn wts(&mut self) -> (WlTransys, WlTsSymbol) {
        panic!("frontend unsupported for wltransys")
    }

    fn safe_certificate(&mut self, proof: McProof) -> Box<dyn Display>;

    fn unsafe_certificate(&mut self, witness: McWitness) -> Box<dyn Display>;

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

pub fn frontend_from_model(model: &PathBuf) -> anyhow::Result<Box<dyn Frontend>> {
    let frontend: Box<dyn Frontend> = match model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => {
            let aig = Aig::from_file(model);
            Box::new(AigFrontend::new(aig))
        }
        Some(ext) if (ext == "btor") | (ext == "btor2") => {
            let btor = Btor::from_file(model);
            Box::new(BtorFrontend::new(btor))
        }
        _ => {
            bail!("Unsupported file format. Supported extensions are: .aig, .aag, .btor, .btor2.");
        }
    };
    Ok(frontend)
}
