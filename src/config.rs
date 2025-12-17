use crate::{
    bmc::BMCConfig, ic3::IC3Config, kind::KindConfig, portfolio::PortfolioConfig,
    rlive::RliveConfig, wlbmc::WlBMCConfig, wlkind::WlKindConfig,
};
use clap::{ArgAction, Args, Parser, Subcommand};
use serde::{Deserialize, Serialize};
use std::ops::Deref;
use strum::AsRefStr;

#[derive(Parser, Debug, Clone, Serialize, Deserialize)]
pub struct EngineConfigBase {
    /// start bound
    #[arg(long = "start", default_value_t = 0)]
    pub start: usize,

    /// max bound to check
    #[arg(long = "end", default_value_t = usize::MAX)]
    pub end: usize,

    /// step length
    #[arg(long, default_value_t = 1, value_parser = clap::value_parser!(u32).range(1..))]
    pub step: u32,

    /// random seed
    #[arg(long, default_value_t = 0)]
    pub rseed: u64,

    /// time limit in seconds
    #[arg(long)]
    pub time_limit: Option<u64>,
}

impl Default for EngineConfigBase {
    fn default() -> Self {
        Self {
            start: 0,
            end: usize::MAX,
            step: 1,
            rseed: 0,
            time_limit: None,
        }
    }
}

#[derive(Parser, Debug, Clone, Serialize, Deserialize)]
pub struct EngineConfig {
    /// model checking engine
    #[command(subcommand)]
    pub engine: Engine,
}

impl Deref for EngineConfig {
    type Target = Engine;

    fn deref(&self) -> &Self::Target {
        &self.engine
    }
}

#[derive(Subcommand, Clone, Debug, Serialize, Deserialize, AsRefStr)]
pub enum Engine {
    /// ic3
    IC3(IC3Config),
    /// k-induction
    Kind(KindConfig),
    /// bmc
    BMC(BMCConfig),
    /// word level bmc
    WlBMC(WlBMCConfig),
    /// word level k-induction
    WlKind(WlKindConfig),
    /// rlive (https://doi.org/10.1007/978-3-031-65627-9_12)
    Rlive(RliveConfig),
    /// portfolio
    Portfolio(PortfolioConfig),
}

impl Engine {
    pub fn is_wl(&self) -> bool {
        matches!(self, Engine::WlBMC(_) | Engine::WlKind(_))
    }
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct PreprocConfig {
    /// disable preprocess
    #[arg(long = "preproc", action = ArgAction::Set, default_value_t = true)]
    pub preproc: bool,

    /// function reduced transys
    #[arg(long = "frts", action = ArgAction::Set, default_value_t = true)]
    pub frts: bool,

    /// frts time limit in seconds
    #[arg(long = "frts-tl", default_value_t = 1000)]
    pub frts_tl: u64,

    /// scorr
    #[arg(long = "scorr", action = ArgAction::Set, default_value_t = true)]
    pub scorr: bool,

    /// scorr time limit in seconds
    #[arg(long = "scorr-tl", default_value_t = 200)]
    pub scorr_tl: u64,
}

impl Default for PreprocConfig {
    fn default() -> Self {
        Self {
            preproc: true,
            frts: true,
            frts_tl: 1000,
            scorr: true,
            scorr_tl: 200,
        }
    }
}
