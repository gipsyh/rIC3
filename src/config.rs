use crate::{
    bmc::BMCConfig, ic3::IC3Config, kind::KindConfig, mp::MultiPropConfig,
    portfolio::PortfolioConfig, rlive::RliveConfig, wlbmc::WlBMCConfig, wlkind::WlKindConfig,
};
use clap::{ArgAction, Args, Parser};
use enum_as_inner::EnumAsInner;
use serde::{Deserialize, Serialize};
use strum::AsRefStr;

/// Macro to implement Deref and DerefMut for config structs that wrap EngineConfigBase
#[macro_export]
macro_rules! impl_config_deref {
    ($config_type:ty) => {
        impl std::ops::Deref for $config_type {
            type Target = $crate::config::EngineConfigBase;

            fn deref(&self) -> &Self::Target {
                &self.base
            }
        }

        impl std::ops::DerefMut for $config_type {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.base
            }
        }
    };
}

#[derive(Parser, Debug, Clone, Serialize, Deserialize)]
pub struct EngineConfigBase {
    /// Property ID. If not specified, all properties are checked.
    #[arg(long = "prop")]
    pub prop: Option<usize>,

    /// Start bound
    #[arg(long = "start", default_value_t = 0)]
    pub start: usize,

    /// Max bound to check
    #[arg(long = "end", default_value_t = usize::MAX)]
    pub end: usize,

    /// Step length
    #[arg(long, default_value_t = 1, value_parser = clap::value_parser!(u32).range(1..))]
    pub step: u32,

    /// Random seed
    #[arg(long, default_value_t = 0)]
    pub rseed: u64,

    /// Time limit in seconds
    #[arg(long)]
    pub time_limit: Option<u64>,
}

impl Default for EngineConfigBase {
    fn default() -> Self {
        Self {
            prop: None,
            start: 0,
            end: usize::MAX,
            step: 1,
            rseed: 0,
            time_limit: None,
        }
    }
}

#[derive(Parser, Clone, Debug, Serialize, Deserialize, AsRefStr, EnumAsInner)]
pub enum EngineConfig {
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
    /// rlive (CAV'24 https://doi.org/10.1007/978-3-031-65627-9_12)
    Rlive(RliveConfig),
    /// Multi-Property (DATE'18 https://doi.org/10.23919/DATE.2018.8341977)
    MultiProp(MultiPropConfig),
    /// portfolio
    Portfolio(PortfolioConfig),
}

impl EngineConfig {
    pub fn is_wl(&self) -> bool {
        matches!(self, EngineConfig::WlBMC(_) | EngineConfig::WlKind(_))
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
