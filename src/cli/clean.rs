use crate::cli::rproj::Ric3Proj;
use giputils::file::remove_if_exists;

pub fn clean() -> anyhow::Result<()> {
    let proj = Ric3Proj::new()?;
    remove_if_exists(proj.path(""))?;
    Ok(())
}
