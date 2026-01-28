use crate::cli::{Ric3Config, cache::Ric3Proj, yosys::Yosys};

pub fn build() -> anyhow::Result<()> {
    let ric3_cfg = Ric3Config::from_file("ric3.toml")?;
    let mut ric3_proj = Ric3Proj::new()?;
    let dut_hash = ric3_cfg.dut.src_hash()?;
    let cached = ric3_proj.check_cached_dut(&dut_hash)?;
    if cached.is_none_or(|c| !c) {
        ric3_proj.clear()?;
        Yosys::generate_btor(&ric3_cfg, ric3_proj.path("dut"))?;
        ric3_proj.cache_dut(&dut_hash)?;
    }
    Ok(())
}
