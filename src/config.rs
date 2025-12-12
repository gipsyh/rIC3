use clap::{ArgAction, Args, Parser, ValueEnum};
use log::error;

#[derive(Parser, Debug, Clone)]
pub struct EngineConfig {
    /// model checking engine
    #[arg(short, long, value_enum, default_value_t = Engine::Portfolio)]
    pub engine: Engine,

    #[command(flatten)]
    pub ic3: IC3Config,

    #[command(flatten)]
    pub bmc: BMCConfig,

    #[command(flatten)]
    pub kind: KindConfig,

    #[command(flatten)]
    pub portfolio: PortfolioConfig,

    #[command(flatten)]
    pub preproc: PreprocessConfig,

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

impl EngineConfig {
    pub fn validate(&self) {
        match self.engine {
            Engine::IC3 => self.ic3.validate(),
            Engine::BMC => {}
            Engine::WlBMC => {}
            Engine::Kind => {}
            Engine::WlKind => {}
            Engine::Rlive => {}
            Engine::Portfolio => {}
        }
    }
}

#[derive(Copy, Clone, ValueEnum, Debug)]
pub enum Engine {
    /// ic3
    IC3,
    /// k-induction
    Kind,
    /// bmc
    BMC,
    /// word level bmc
    WlBMC,
    /// word level k-induction
    WlKind,
    /// rlive (https://doi.org/10.1007/978-3-031-65627-9_12)
    Rlive,
    /// portfolio
    Portfolio,
}

impl Engine {
    pub fn is_wl(&self) -> bool {
        matches!(self, Engine::WlBMC | Engine::WlKind)
    }
}

#[derive(Args, Clone, Debug)]
pub struct IC3Config {
    /// dynamic generalization
    #[arg(long = "ic3-dynamic", default_value_t = false)]
    pub dynamic: bool,

    /// ic3 with counterexample to generalization
    #[arg(long = "ic3-ctg", action = ArgAction::Set, default_value_t = true)]
    pub ctg: bool,

    /// max number of ctg
    #[arg(long = "ic3-ctg-max", default_value_t = 3)]
    pub ctg_max: usize,

    /// ctg limit
    #[arg(long = "ic3-ctg-limit", default_value_t = 1)]
    pub ctg_limit: usize,

    /// ic3 counterexample to propagation
    #[arg(long = "ic3-ctp", default_value_t = false)]
    pub ctp: bool,

    /// ic3 with internal signals (FMCAD'21)
    #[arg(long = "ic3-inn", default_value_t = false)]
    pub inn: bool,

    /// ic3 with abstract constrains
    #[arg(long = "ic3-abs-cst", default_value_t = false)]
    pub abs_cst: bool,

    /// ic3 with abstract trans
    #[arg(long = "ic3-abs-trans", default_value_t = false)]
    pub abs_trans: bool,

    /// ic3 with dropping proof-obligation
    #[arg(
        long = "ic3-drop-po", action = ArgAction::Set, default_value_t = true,
    )]
    pub drop_po: bool,

    /// ic3 full assignment of last bad (used in rlive)
    #[arg(long = "ic3-full-bad", default_value_t = false)]
    pub full_bad: bool,

    /// ic3 with abstract array
    #[arg(long = "ic3-abs-array", default_value_t = false)]
    pub abs_array: bool,

    /// ic3 with finding parent lemma in mic
    #[arg(long = "ic3-parent-lemma", action = ArgAction::Set, default_value_t = true)]
    pub parent_lemma: bool,
}

impl IC3Config {
    pub fn validate(&self) {
        if self.dynamic && self.drop_po {
            error!("cannot enable both ic3-dynamic and ic3-drop-po");
            panic!();
        }
    }
}

#[derive(Args, Clone, Debug)]
pub struct BMCConfig {
    /// Per-step time limit for BMC (applies to each BMC step, not the overall solver run).
    /// The overall `time_limit` option sets the total time limit for the entire solver run.
    #[arg(long = "bmc-time-limit")]
    pub step_time_limit: Option<u64>,
    /// use kissat solver in bmc, otherwise cadical
    #[arg(long = "bmc-kissat", default_value_t = false)]
    pub bmc_kissat: bool,
    /// bmc dynamic step
    #[arg(long = "bmc-dyn-step", default_value_t = false)]
    pub dyn_step: bool,
}

#[derive(Args, Clone, Debug)]
pub struct KindConfig {
    /// simple path constraint
    #[arg(long = "kind-simple-path", default_value_t = false)]
    pub simple_path: bool,
}

#[derive(Args, Clone, Debug)]
pub struct PreprocessConfig {
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

#[derive(Args, Clone, Debug)]
pub struct PortfolioConfig {
    /// portfolio woker memory limit in GB
    #[arg(long = "pworker-mem-limit", default_value_t = 16)]
    pub wmem_limit: usize,
}

impl Default for EngineConfig {
    fn default() -> Self {
        EngineConfig::parse_from([""])
    }
}
