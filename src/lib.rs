#![allow(non_snake_case)]

pub mod bmc;
pub mod config;
pub mod frontend;
mod gipsat;
pub mod ic3;
pub mod kind;
pub mod mp;
pub mod portfolio;
pub mod rlive;
pub mod tracer;
pub mod transys;
pub mod wlbmc;
pub mod wlkind;
pub mod wltransys;

use crate::{
    tracer::TracerIf,
    transys::certify::{BlProof, BlWitness},
    wltransys::certify::{WlProof, WlWitness},
};
use enum_as_inner::EnumAsInner;
use serde::{Deserialize, Serialize};
use std::sync::{Arc, atomic::AtomicBool};

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

#[derive(Clone, Debug, EnumAsInner)]
pub enum McProof {
    Bl(BlProof),
    Wl(WlProof),
}

#[derive(Clone, Debug, EnumAsInner)]
pub enum McWitness {
    Bl(BlWitness),
    Wl(WlWitness),
}

pub trait Engine: Send {
    fn check(&mut self) -> McResult;

    fn add_tracer(&mut self, _tracer: Box<dyn TracerIf>) {}

    fn statistic(&mut self) {}

    fn proof(&mut self) -> McProof {
        panic!("unsupport proof");
    }

    fn witness(&mut self) -> McWitness {
        panic!("unsupport witness");
    }

    fn get_stop_ctrl(&self) -> Arc<AtomicBool> {
        panic!("unsupport getting stop ctrl");
    }
}
