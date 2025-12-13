#![feature(ptr_metadata)]

mod cli;

use crate::cli::cli_main;
use std::fs;

fn main() -> anyhow::Result<()> {
    fs::create_dir_all("/tmp/rIC3")?;
    cli_main()
}
