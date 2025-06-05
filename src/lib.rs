#![allow(non_snake_case)]
#![feature(get_mut_unchecked)]

pub mod bmc;
pub mod config;
pub mod frontend;
mod gipsat;
pub mod ic3;
pub mod kind;
pub mod portfolio;
pub mod transys;

use config::Config;
use logic_form::{LitVec, Var};
use transys::Transys;

#[derive(Clone, Debug, Default)]
pub struct Witness {
    pub init: LitVec,
    pub wit: Vec<LitVec>,
}

impl Witness {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn map_var(&self, f: impl Fn(Var) -> Var) -> Self {
        let init = self.init.map_var(&f);
        let wit = self.wit.iter().map(|w| w.map_var(&f)).collect();
        Self { init, wit }
    }
}

pub struct Proof {
    pub proof: Transys,
}

pub trait Engine {
    fn check(&mut self) -> Option<bool>;

    fn proof(&mut self) -> Proof {
        panic!("unsupport proof");
    }

    fn witness(&mut self) -> Witness {
        panic!("unsupport witness");
    }

    fn statistic(&mut self) {}
}
