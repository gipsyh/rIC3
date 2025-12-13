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
pub mod tracer;
pub mod transys;
pub mod wlbmc;
pub mod wlkind;
pub mod wltransys;

use crate::{
    tracer::TracerIf,
    transys::certify::{Proof, Witness},
    wltransys::certify::{WlProof, WlWitness},
};
use config::EngineConfig;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Clone, Copy, Debug)]
pub enum McResult {
    /// Safe
    Safe,
    /// Unsafe with Cex Depth
    Unsafe(usize),
    /// Proved in Some(exact depth)
    Unknown(Option<usize>),
}

impl Default for McResult {
    fn default() -> Self {
        McResult::Unknown(None)
    }
}

pub trait Engine {
    fn check(&mut self) -> Option<bool>;

    fn add_tracer(&mut self, _tracer: Box<dyn TracerIf>) {
        panic!("unsupport adding tracer");
    }

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
