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
pub mod wlbmc;
pub mod wltransys;

use crate::{
    transys::certify::{Proof, Witness},
    wltransys::certify::{WlProof, WlWitness},
};
use config::Config;

pub trait Engine {
    fn check(&mut self) -> Option<bool>;

    fn statistic(&mut self) {}

    fn is_wl(&self) -> bool {
        false
    }

    fn proof(&mut self) -> Proof {
        panic!("unsupport proof");
    }

    fn witness(&mut self) -> Witness {
        panic!("unsupport witness");
    }

    fn wl_proof(&mut self) -> WlProof {
        assert!(self.is_wl());
        panic!("unsupport proof");
    }

    fn wl_witness(&mut self) -> WlWitness {
        assert!(self.is_wl());
        panic!("unsupport witness");
    }
}
