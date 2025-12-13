#![feature(ptr_metadata)]

mod cli;

use crate::cli::cli_main;
use std::{env, fs};

fn main() -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .format_target(false)
        .init();
    fs::create_dir_all("/tmp/rIC3")?;
    cli_main()
}
