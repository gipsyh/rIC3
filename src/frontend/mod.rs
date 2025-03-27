use crate::transys::Transys;
pub mod abc;
pub mod aig;

pub trait Frontend {
    fn ts(&self) -> Transys;

    fn certifate(&self);
}