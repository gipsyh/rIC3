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
use logic_form::LitVec;
use transys::Transys;

#[derive(Clone, Debug, Default)]
pub struct Witness {
    pub init: LitVec,
    pub wit: Vec<LitVec>,
}

pub struct Proof {
    pub proof: Transys,
}

pub trait Engine {
    fn check(&mut self) -> Option<bool>;

    fn proof(&mut self, _ts: &Transys) -> Proof {
        panic!("unsupport certifaiger");
    }

    fn witness(&mut self, _ts: &Transys) -> Witness {
        panic!("unsupport witness");
    }

    fn statistic(&mut self) {}
}
