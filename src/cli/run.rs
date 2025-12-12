use crate::cli::{cache::Ric3Proj, yosys::Yosys};
use clap::Parser;
use serde::Deserialize;
use std::{
    error::{self, Error},
    fs,
    path::{Path, PathBuf},
};

#[derive(Deserialize, Debug)]
pub struct Ric3Config {
    pub dut: Dut,
}

impl Ric3Config {
    pub fn from_file<P: AsRef<Path>>(p: P) -> Result<Self, Box<dyn Error>> {
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

pub fn run() -> Result<(), Box<dyn error::Error>> {
    let ric3_cfg = Ric3Config::from_file("ric3.toml")?;
    let ric3_proj = Ric3Proj::new()?;
    let same = ric3_proj.check_cached_src(&ric3_cfg.dut_src())?;
    if same {
    } else {
        ric3_proj.clear()?;
        Yosys::generate_btor(&ric3_cfg, &ric3_proj);
        ric3_proj.cache_src(&ric3_cfg.dut_src())?;
    }
    let btor = ric3_proj.dut_path().join("dut.btor");
    let ric3_cfg =
        rIC3::config::EngineConfig::parse_from(["", "-e", "ic3", &format!("{}", btor.display())]);
    todo!()
    // check(ric3_cfg)
}
