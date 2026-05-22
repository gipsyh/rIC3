use crate::cli::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use anyhow::Context;
use giputils::file::{recreate_dir, remove_if_exists};
use log::info;
use std::{
    path::{Path, PathBuf},
    process::Command,
};

fn shadow_link_script() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tools/shadow_link_invariants.py")
}

fn link_btor(dut_dir: &Path, helpers_dir: &Path) -> anyhow::Result<()> {
    let script = shadow_link_script();
    info!(
        "CIll link: linking helper artifacts with {}.",
        script.display()
    );
    let output = Command::new("python3")
        .arg(&script)
        .arg("--core")
        .arg(dut_dir.join("dut.btor"))
        .arg("--monitor")
        .arg(helpers_dir.join("monitor.btor"))
        .arg("--link-map")
        .arg(dut_dir.join("link_map.json"))
        .arg("--linked")
        .arg(helpers_dir.join("linked.btor"))
        .output()
        .with_context(|| format!("failed to run {}", script.display()))?;
    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!(
            "shadow link failed with status {}.\n{}\n{}",
            output.status,
            stdout,
            stderr
        );
    }
    Ok(())
}

pub fn link(rcfg: Ric3Config, rp: Ric3Proj, invariants: PathBuf) -> anyhow::Result<()> {
    if !rcfg.dut.defines.is_empty() {
        anyhow::bail!("`ric3 cill link` does not support dut.defines");
    }
    if !invariants.exists() {
        anyhow::bail!("invariants file not found: {}", invariants.display());
    }
    let dut_dir = rp.path("cill/dut");
    let shadow = dut_dir.join("shadow.sv");
    let link_map = dut_dir.join("link_map.json");
    let core = dut_dir.join("dut.btor");
    for path in [&shadow, &link_map, &core] {
        if !path.exists() {
            anyhow::bail!(
                "missing prepared DUT artifact: {}. Run `ric3 cill prepare` first.",
                path.display()
            );
        }
    }

    let helpers_dir = rp.path("cill/helpers");
    recreate_dir(&helpers_dir)?;
    remove_if_exists(helpers_dir.join("linked.btor"))?;
    Yosys::generate_btor_with_files(&rcfg, &[shadow, invariants], &helpers_dir, "monitor")?;
    link_btor(&dut_dir, &helpers_dir)?;
    println!(
        "CIll helper artifacts generated in {}.",
        helpers_dir.display()
    );
    Ok(())
}
