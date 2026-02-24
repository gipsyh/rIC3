#![allow(non_snake_case)]

pub mod bmc;
pub mod config;
pub mod frontend;
pub mod gipsat;
pub mod ic3;
pub mod kind;
pub mod mp;
pub mod polynexus;
pub mod portfolio;
pub mod rlive;
pub mod tracer;
pub mod transys;
pub mod wlbmc;
pub mod wlkind;
pub mod wltransys;

use crate::{
    config::EngineConfig,
    tracer::TracerIf,
    transys::{
        Transys,
        certify::{BlProof, BlWitness},
    },
    wltransys::{
        WlTransys,
        certify::{WlProof, WlWitness},
    },
};
use enum_as_inner::EnumAsInner;
use serde::{Deserialize, Serialize};
use std::{
    ops::BitOr,
    sync::{Arc, atomic::AtomicBool},
};

#[derive(Serialize, Deserialize, Clone, Copy, Debug, PartialEq, EnumAsInner)]
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

impl BitOr for McResult {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        use McResult::*;
        match (self, rhs) {
            (Safe, Unsafe(_)) | (Unsafe(_), Safe) => {
                panic!("conflicting results: safe and unsafe")
            }
            (Safe, _) | (_, Safe) => Safe,
            (Unsafe(a), Unsafe(b)) => Unsafe(a.max(b)),
            (Unsafe(a), Unknown(_)) | (Unknown(_), Unsafe(a)) => Unsafe(a),
            (Unknown(a), Unknown(b)) => Unknown(match (a, b) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            }),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MpMcResult(Vec<McResult>);

impl MpMcResult {
    pub fn new(size: usize) -> Self {
        Self(vec![McResult::default(); size])
    }

    pub fn iter(&self) -> impl Iterator<Item = &McResult> {
        self.0.iter()
    }
}

impl std::ops::Index<usize> for MpMcResult {
    type Output = McResult;
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl std::ops::IndexMut<usize> for MpMcResult {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl FromIterator<McResult> for MpMcResult {
    fn from_iter<I: IntoIterator<Item = McResult>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
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

pub trait MpEngine: Engine {
    fn check(&mut self) -> MpMcResult;

    fn witness(&mut self, _prop: usize) -> McWitness {
        panic!("unsupport witness");
    }

    fn proof(&mut self, _prop: usize) -> McProof {
        panic!("unsupport proof");
    }
}

pub fn create_bl_engine(
    cfg: EngineConfig,
    ts: Transys,
    sym: logicrs::VarSymbols,
) -> Box<dyn Engine> {
    let num_bad = ts.bad.len();
    match cfg {
        EngineConfig::IC3(cfg) => Box::new(ic3::IC3::new(cfg, ts, sym)),
        EngineConfig::Kind(cfg) => Box::new(kind::Kind::new(cfg, ts)),
        EngineConfig::BMC(cfg) => Box::new(bmc::BMC::new(cfg, ts)),
        EngineConfig::MultiProp(cfg) => Box::new(mp::MultiProp::new(cfg, ts)),
        EngineConfig::Rlive(cfg) => Box::new(rlive::Rlive::new(cfg, ts)),
        EngineConfig::Polynexus(cfg) => {
            Box::new(polynexus::PolyNexus::new(cfg, ts, MpMcResult::new(num_bad)))
        }
        _ => unreachable!(),
    }
}

pub fn create_wl_engine(cfg: EngineConfig, ts: WlTransys) -> Box<dyn Engine> {
    match cfg {
        EngineConfig::WlBMC(cfg) => Box::new(wlbmc::WlBMC::new(cfg, ts)),
        EngineConfig::WlKind(cfg) => Box::new(wlkind::WlKind::new(cfg, ts)),
        _ => unreachable!(),
    }
}
