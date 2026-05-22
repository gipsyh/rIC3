use crate::cli::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use anyhow::Context;
use giputils::file::recreate_dir;
use log::info;
use std::{
    path::{Path, PathBuf},
    process::Command,
};

fn shadow_prepare_script() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tools/shadow_prepare.py")
}

fn generate_shadow(rcfg: &Ric3Config, out_dir: &Path) -> anyhow::Result<()> {
    let script = shadow_prepare_script();
    info!(
        "CIll prepare: generating shadow artifacts with {}.",
        script.display()
    );
    let mut cmd = Command::new("python3");
    cmd.arg(&script).arg("--top").arg(&rcfg.dut.top);
    for file in &rcfg.dut.files {
        cmd.arg("--file").arg(file);
    }
    let output = cmd
        .arg("--out")
        .arg(out_dir)
        .output()
        .with_context(|| format!("failed to run {}", script.display()))?;
    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!(
            "shadow prepare failed with status {}.\n{}\n{}",
            output.status,
            stdout,
            stderr
        );
    }
    Ok(())
}

pub fn prepare(rcfg: Ric3Config, rp: Ric3Proj) -> anyhow::Result<()> {
    if !rcfg.dut.defines.is_empty() {
        anyhow::bail!("`ric3 cill prepare` does not support dut.defines");
    }
    let out_dir = rp.path("cill/dut");
    recreate_dir(&out_dir)?;
    Yosys::generate_btor(&rcfg, &out_dir)?;
    generate_shadow(&rcfg, &out_dir)?;
    println!("CIll prepare artifacts generated in {}.", out_dir.display());
    Ok(())
}
