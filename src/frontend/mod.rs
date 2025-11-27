use crate::{Proof, Witness, transys::Transys};
use logicrs::VarSymbols;
use std::{fmt::Display, path::Path};

pub mod aig;
pub mod btor;

pub trait Frontend {
    fn ts(&mut self) -> (Transys, VarSymbols);

    fn safe_certificate(&mut self, proof: Proof) -> Box<dyn Display>;

    fn unsafe_certificate(&mut self, witness: Witness) -> Box<dyn Display>;

    fn certify(&mut self, model: &Path, cert: &Path) -> bool;
}
