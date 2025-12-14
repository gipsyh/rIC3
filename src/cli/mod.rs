mod cache;
mod check;
mod clean;
mod ctilg;
mod run;
mod yosys;

use crate::cli::{check::CheckConfig, clean::clean, ctilg::ctilg};
use clap::{Parser, Subcommand};
use rIC3::config::EngineConfig;
use serde::Deserialize;
use std::{
    fs,
    path::{Path, PathBuf},
};

/// rIC3 Hardware Formal Verification Tool
#[derive(Parser, Debug, Clone)]
#[command(
    version,
    about,
    after_help = "Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved."
)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand, Debug, Clone)]
pub enum Commands {
    Run,
    Check {
        #[command(flatten)]
        chk: CheckConfig,

        #[command(flatten)]
        cfg: EngineConfig,
    },
    Clean,
    Ctilg,
}

pub fn cli_main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Run => run::run(),
        Commands::Check { chk, cfg } => check::check(chk, cfg),
        Commands::Clean => clean(),
        Commands::Ctilg => ctilg(),
    }
}

#[derive(Deserialize, Debug)]
pub struct Ric3Config {
    pub dut: Dut,
}

impl Ric3Config {
    pub fn from_file<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let config_content = fs::read_to_string(p)?;
        let config: Self = toml::from_str(&config_content)?;
        Ok(config)
    }

    pub fn dut_src(&self) -> Vec<PathBuf> {
        self.dut.files.clone()
    }
}

#[derive(Deserialize, Debug)]
pub struct Dut {
    pub top: String,
    pub files: Vec<PathBuf>,
}
