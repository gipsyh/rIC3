use clap::{Args, Parser, ValueEnum};
use std::path::PathBuf;

/// rIC3 model checker
#[derive(Parser, Debug, Clone)]
#[command(
    version,
    about,
    after_help = "Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved."
)]
pub struct Config {
    /// model checking engine
    #[arg(short, long, value_enum, default_value_t = Engine::Portfolio)]
    pub engine: Engine,

    /// model file in aiger format or in btor2 format.
    /// for btor model, the file name should be suffixed with .btor or .btor2
    pub model: PathBuf,

    /// certificate path
    pub certificate: Option<PathBuf>,

    /// certify with certifaiger
    #[arg(long, default_value_t = false)]
    pub certify: bool,

    /// print witness when model is unsafe
    #[arg(long, default_value_t = false)]
    pub witness: bool,

    #[command(flatten)]
    pub ic3: IC3Options,

    #[command(flatten)]
    pub bmc: BMCOptions,

    #[command(flatten)]
    pub kind: KindOptions,

    #[command(flatten)]
    pub portfolio: PortfolioOptions,

    #[command(flatten)]
    pub preprocess: PreprocessOptions,

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

    /// interrupt statistic
    #[arg(long, default_value_t = false)]
    pub interrupt_statistic: bool,
}

#[derive(Copy, Clone, ValueEnum, Debug)]
pub enum Engine {
    /// ic3
    IC3,
    /// k-induction
    Kind,
    /// bmc
    BMC,
    /// rlive (https://doi.org/10.1007/978-3-031-65627-9_12)
    Rlive,
    /// portfolio
    Portfolio,
}

#[derive(Args, Clone, Debug)]
pub struct IC3Options {
    /// dynamic generalization
    #[arg(long = "ic3-dynamic", default_value_t = false)]
    pub dynamic: bool,

    /// ic3 counterexample to generalization
    #[arg(long = "ic3-no-ctg", default_value_t = false)]
    pub no_ctg: bool,

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

    /// ic3 without predicate property
    #[arg(long = "ic3-no-pred-prop", default_value_t = false)]
    pub no_pred_prop: bool,

    /// ic3 full assignment of last bad (used in rlive)
    #[arg(long = "ic3-full-bad", default_value_t = false)]
    pub full_bad: bool,
}

#[derive(Args, Clone, Debug)]
pub struct BMCOptions {
    /// bmc single step time limit
    #[arg(long = "bmc-time-limit")]
    pub time_limit: Option<u64>,
    /// use kissat solver, otherwise cadical
    #[arg(long = "bmc-kissat", default_value_t = false)]
    pub bmc_kissat: bool,
}

#[derive(Args, Clone, Debug)]
pub struct KindOptions {
    /// no bmc check in kind
    #[arg(long = "kind-no-bmc", default_value_t = false)]
    pub no_bmc: bool,
    /// use kissat solver, otherwise cadical
    #[arg(long = "kind-kissat", default_value_t = false)]
    pub kind_kissat: bool,
    /// simple path constraint
    #[arg(long = "kind-simple-path", default_value_t = false)]
    pub simple_path: bool,
}

#[derive(Args, Clone, Debug)]
pub struct PreprocessOptions {
    /// sec preprocess
    #[arg(long = "sec", default_value_t = false)]
    pub sec: bool,

    /// disable abc preprocess
    #[arg(long = "no-abc", default_value_t = false)]
    pub no_abc: bool,
}

#[derive(Args, Clone, Debug)]
pub struct PortfolioOptions {
    /// portfolio woker memory limit in GB
    #[arg(long = "pworker-mem-limit", default_value_t = 16)]
    pub wmem_limit: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config::parse_from([""])
    }
}
