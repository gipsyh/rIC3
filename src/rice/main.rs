mod config;
mod proj;
mod yosys;

use crate::config::RiceConfig;
use crate::proj::RiceProj;
use crate::yosys::Yosys;
use std::error::Error;
use std::fs;
use std::path::Path;

fn main() -> Result<(), Box<dyn Error>> {
    let riceconfig = RiceConfig::from_file("rice.toml")?;
    let riceproj_dir = "riceproj";
    if !Path::new(riceproj_dir).exists() {
        fs::create_dir(riceproj_dir)?;
    }
    let riceproj = RiceProj::new()?;
    let same = riceproj.check_cached_src(&riceconfig.dut_src())?;
    if same {
    } else {
        riceproj.clear()?;
        Yosys::generate_btor(&riceconfig, &riceproj);
        riceproj.cache_src(&riceconfig.dut_src())?;
    }
    Ok(())
}
