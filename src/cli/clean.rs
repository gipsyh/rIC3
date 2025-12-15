use crate::cli::cache::Ric3Proj;
use std::fs;

pub fn clean() -> anyhow::Result<()> {
    let proj = Ric3Proj::new()?;
    if proj.path("").exists() {
        fs::remove_dir_all(proj.path(""))?;
    }
    Ok(())
}
