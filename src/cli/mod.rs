mod cache;
mod check;
mod clean;
mod ctilg;
mod run;
mod yosys;

use crate::cli::{check::CheckConfig, clean::clean, ctilg::ctilg};
use clap::{Parser, Subcommand};
use giputils::hash::GHashSet;
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
    /// Run verification using 'ric3.toml' (requires the file in the current directory)
    Run,

    /// Verify properties for AIGER/BTOR files with custom configurations
    Check {
        #[command(flatten)]
        chk: CheckConfig,

        #[command(flatten)]
        cfg: EngineConfig,
    },

    /// Clean up verification cache and artifacts
    Clean,

    /// CTI Guided Interactive Lemma Generation
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
    fn from_file<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let config_content = fs::read_to_string(p)?;
        let config: Self = toml::from_str(&config_content)?;
        config.dut.validate()?;
        Ok(config)
    }
}

#[derive(Deserialize, Debug)]
pub struct Dut {
    pub top: String,
    pub files: Vec<PathBuf>,
    pub include_files: Option<Vec<PathBuf>>,
}

impl Dut {
    fn src(&self) -> Vec<PathBuf> {
        self.files
            .iter()
            .chain(self.include_files.iter().flatten())
            .cloned()
            .collect()
    }

    fn validate(&self) -> anyhow::Result<()> {
        if self.files.is_empty() {
            anyhow::bail!("dut files cannot be empty");
        }
        let mut seen_names = GHashSet::new();
        let files = self.src();
        for file in files.iter() {
            if !file.exists() {
                anyhow::bail!("file not found: {:?}", file);
            }
            if let Some(name) = file.file_name() {
                if !seen_names.insert(name) {
                    anyhow::bail!("duplicate file name found: {:?}", name);
                }
            } else {
                anyhow::bail!("invalid file path: {:?}", file);
            }
        }
        Ok(())
    }
}
