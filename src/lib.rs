#![allow(non_snake_case)]
#![feature(get_mut_unchecked, likely_unlikely)]

pub mod bmc;
pub mod config;
pub mod frontend;
mod gipsat;
pub mod ic3;
pub mod kind;
pub mod portfolio;
pub mod rlive;
pub mod transys;
pub mod wltransys;

use crate::transys::certify::{Proof, Witness};
use config::Config;

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
