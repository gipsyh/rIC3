mod cache;
mod check;
mod run;
mod yosys;

use crate::cli::check::CheckConfig;
use clap::{Parser, Subcommand};
use rIC3::config::EngineConfig;

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
    Interact,
}

pub fn cli_main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Run => run::run(),
        Commands::Check { chk, cfg } => check::check(chk, cfg),
        Commands::Clean => todo!(),
        Commands::Interact => todo!(),
    }
}
