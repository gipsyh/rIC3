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
        certify::{BlCex, BlProof},
    },
    wltransys::{
        WlTransys,
        certify::{WlCex, WlProof},
    },
};
use enum_as_inner::EnumAsInner;
use serde::{Deserialize, Serialize};
use std::{
    ops::BitOr,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

/// External control handle for engines.
#[derive(Clone, Debug)]
pub struct EngineCtrl {
    terminate: Arc<AtomicBool>,
    // TODO: implement stop/resume support
    #[allow(dead_code)]
    stop: Arc<AtomicBool>,
    #[allow(dead_code)]
    resume: Arc<AtomicBool>,
}

impl Default for EngineCtrl {
    fn default() -> Self {
        Self {
            terminate: Arc::new(AtomicBool::new(false)),
            stop: Arc::new(AtomicBool::new(false)),
            resume: Arc::new(AtomicBool::new(false)),
        }
    }
}

impl EngineCtrl {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn terminate(&self) {
        self.terminate.store(true, Ordering::Relaxed);
    }

    pub fn is_terminated(&self) -> bool {
        self.terminate.load(Ordering::Relaxed)
    }

    pub fn stop(&self) {
        todo!("stop not yet implemented");
    }

    pub fn is_stopped(&self) -> bool {
        todo!("is_stopped not yet implemented");
    }

    pub fn resume(&self) {
        todo!("resume not yet implemented");
    }
}

#[derive(Serialize, Deserialize, Clone, Copy, Debug, PartialEq, EnumAsInner)]
pub enum McResult {
    /// Property is Satisfied
    Satisfied,
    /// Property is Violated with Cex Depth
    Violated(usize),
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
            (Satisfied, Violated(_)) | (Violated(_), Satisfied) => {
                panic!("conflicting results: satisfied and violated")
            }
            (Satisfied, _) | (_, Satisfied) => Satisfied,
            (Violated(a), Violated(b)) => Violated(a.max(b)),
            (Violated(a), Unknown(_)) | (Unknown(_), Violated(a)) => Violated(a),
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

#[derive(Clone, Debug, EnumAsInner, Serialize, Deserialize)]
pub enum McBlCertificate {
    Satisfied(BlProof),
    Violated(BlCex),
}

#[derive(Clone, Debug, EnumAsInner)]
pub enum McWlCertificate {
    Satisfied(WlProof),
    Violated(WlCex),
}

pub trait Engine: Send {
    fn check(&mut self) -> McResult;

    fn add_tracer(&mut self, _tracer: Box<dyn TracerIf>) {}

    fn statistic(&mut self) {}

    fn get_ctrl(&self) -> EngineCtrl {
        panic!("unsupport get_ctrl");
    }
}

pub trait BlEngine: Engine {
    fn proof(&mut self) -> BlProof {
        panic!("unsupport proof");
    }

    fn cex(&mut self) -> BlCex {
        panic!("unsupport counterexample");
    }

    fn certificate(&mut self, res: McResult) -> McBlCertificate {
        match res {
            McResult::Satisfied => McBlCertificate::Satisfied(self.proof()),
            McResult::Violated(_) => McBlCertificate::Violated(self.cex()),
            McResult::Unknown(_) => panic!(),
        }
    }
}

pub trait WlEngine: Engine {
    fn proof(&mut self) -> WlProof {
        panic!("unsupport proof");
    }

    fn cex(&mut self) -> WlCex {
        panic!("unsupport counterexample");
    }

    fn certificate(&mut self, res: McResult) -> McWlCertificate {
        match res {
            McResult::Satisfied => McWlCertificate::Satisfied(self.proof()),
            McResult::Violated(_) => McWlCertificate::Violated(self.cex()),
            McResult::Unknown(_) => panic!(),
        }
    }
}

pub trait MpEngine: Engine {
    fn check(&mut self) -> MpMcResult;

    fn cex(&mut self, _prop: usize) -> BlCex {
        panic!("unsupport counterexample");
    }

    fn proof(&mut self, _prop: usize) -> BlProof {
        panic!("unsupport proof");
    }
}

pub fn create_bl_engine(
    cfg: EngineConfig,
    ts: Transys,
    sym: logicrs::VarSymbols,
) -> Box<dyn BlEngine> {
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

pub fn create_wl_engine(cfg: EngineConfig, ts: WlTransys) -> Box<dyn WlEngine> {
    match cfg {
        EngineConfig::WlBMC(cfg) => Box::new(wlbmc::WlBMC::new(cfg, ts)),
        EngineConfig::WlKind(cfg) => Box::new(wlkind::WlKind::new(cfg, ts)),
        _ => unreachable!(),
    }
}
