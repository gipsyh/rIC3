#![feature(ptr_metadata)]

mod cli;

use crate::cli::Cli;
use clap::Parser;
use std::{env, error, fs};

fn main() -> Result<(), Box<dyn error::Error>> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .format_target(false)
        .init();
    fs::create_dir_all("/tmp/rIC3")?;

    let cli = Cli::parse();
    match cli.command {
        cli::Commands::Run => todo!(),
        cli::Commands::Check(cfg) => cli::check(cfg),
        cli::Commands::Clean => todo!(),
        cli::Commands::Interact => todo!(),
    }
}
