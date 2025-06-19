use crate::{Engine, transys::Transys};

pub mod aig;
pub mod btor;

pub trait Frontend {
    fn ts(&mut self) -> Transys;

    fn certificate_safe(&mut self, engine: &mut dyn Engine);

    fn certificate_unsafe(&mut self, engine: &mut dyn Engine);
}
