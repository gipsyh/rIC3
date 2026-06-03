mod build;
mod check;
mod cill;
mod clean;
mod rproj;
mod run;
mod trace;
mod vcd;
mod yosys;

use crate::cli::{
    check::CheckConfig,
    cill::{CIllCommands, cill},
    rproj::DutHash,
    trace::{TraceCommands, trace},
};
use anyhow::Context;
use clap::{Parser, Subcommand};
use giputils::hash::{GHashMap, GHashSet};
use rIC3::config::EngineConfig;
use serde::Deserialize;
use std::{
    fs,
    io::ErrorKind,
    iter::once,
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
    Run {
        #[command(flatten)]
        cfg: run::RunConfig,
    },

    /// Verify properties for AIGER/BTOR files
    Check {
        #[command(flatten)]
        chk: CheckConfig,

        #[command(subcommand)]
        cfg: EngineConfig,
    },

    /// Clean up verification cache (ric3proj)
    Clean,

    /// Build ric3proj with ric3.toml
    Build,

    /// CTI Guided Interactive Lemma Generation
    Cill {
        #[command(subcommand)]
        cmd: CIllCommands,
    },

    /// Inspect Traces (CounterExamples or CTIs).
    Trace {
        #[command(subcommand)]
        cmd: TraceCommands,
    },
}

pub fn cli_main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Run { cfg } => run::run(cfg),
        Commands::Build => build::build(),
        Commands::Check { chk, cfg } => check::check(chk, cfg),
        Commands::Clean => clean::clean(),
        Commands::Cill { cmd } => cill(cmd),
        Commands::Trace { cmd } => trace(cmd),
    }
}

#[derive(Deserialize, Debug)]
pub struct Ric3Config {
    dut: Dut,
    modeling: Option<Modeling>,
    formal: Option<FormalConfig>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct FormalConfig {
    pub(crate) invariants: Option<PathBuf>,
}

impl FormalConfig {
    fn validate(&self) -> anyhow::Result<()> {
        if let Some(invariants) = &self.invariants
            && !invariants.exists()
        {
            anyhow::bail!("formal invariants file not found: {:?}", invariants);
        }
        Ok(())
    }
}

impl Ric3Config {
    fn from_file<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let path = p.as_ref();
        let config_content = match fs::read_to_string(path) {
            Ok(content) => content,
            Err(err) if err.kind() == ErrorKind::NotFound => {
                anyhow::bail!(
                    "missing config file: {}. Expected a ric3.toml in the current directory.",
                    path.display()
                );
            }
            Err(err) => {
                return Err(err)
                    .with_context(|| format!("failed to read config file: {}", path.display()));
            }
        };
        let config: Self = toml::from_str(&config_content)?;
        config.dut.validate()?;
        if let Some(formal) = &config.formal {
            formal.validate()?;
        }
        Ok(config)
    }

    fn reset(&self) -> Option<(String, bool)> {
        let reset = self.dut.reset.clone()?;
        Some(if reset.starts_with("!") {
            let reset = reset.strip_prefix("!").unwrap();
            (reset.to_string(), false)
        } else {
            (reset.to_string(), true)
        })
    }
}

#[derive(Deserialize, Debug)]
struct Dut {
    reset: Option<String>,
    top: String,
    files: Vec<PathBuf>,
    include_files: Option<Vec<PathBuf>>,
    #[serde(default)]
    defines: GHashMap<String, String>,
}

#[derive(Deserialize, Debug)]
struct Modeling {
    parser: Parse,
}

#[derive(Deserialize, Debug)]
#[allow(non_camel_case_types)]
enum Parse {
    yosys,
    yosys_slang,
}

impl Dut {
    fn src(&self) -> Vec<PathBuf> {
        self.files
            .iter()
            .chain(self.include_files.iter().flatten())
            .cloned()
            .chain(once(PathBuf::from("ric3.toml")))
            .collect()
    }

    fn src_hash(&self) -> anyhow::Result<DutHash> {
        DutHash::new(&self.src())
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
