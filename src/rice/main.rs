mod cache;
mod cli;
mod config;
mod prop;
mod yosys;

use crate::cache::RiceProj;
use crate::config::RiceConfig;
use crate::yosys::Yosys;
use clap::Parser;
use rIC3::ric3_check;
use std::error::Error;
use std::path::Path;
use std::{env, fs};

fn set_logger() {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .format_target(false)
        .init();
}

fn main() -> Result<(), Box<dyn Error>> {
    set_logger();
    let rice_cfg = RiceConfig::from_file("rice.toml")?;
    if !Path::new("riceproj").exists() {
        fs::create_dir("riceproj")?;
    }
    let rice_proj = RiceProj::new()?;
    let same = rice_proj.check_cached_src(&rice_cfg.dut_src())?;
    if same {
    } else {
        rice_proj.clear()?;
        Yosys::generate_btor(&rice_cfg, &rice_proj);
        rice_proj.cache_src(&rice_cfg.dut_src())?;
    }
    let btor = rice_proj.dut_path().join("dut.btor");
    let ric3_cfg =
        rIC3::config::Config::parse_from(["", "-e", "ic3", &format!("{}", btor.display())]);
    let res = ric3_check(ric3_cfg);
    // rice_proj
    Ok(())
}
