use std::{
    error::Error,
    fs,
    path::{Path, PathBuf},
};

use serde::Deserialize;

#[derive(Deserialize, Debug)]
pub struct RiceConfig {
    pub dut: Dut,
}

impl RiceConfig {
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
