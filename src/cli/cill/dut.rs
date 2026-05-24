use crate::cli::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use anyhow::Context;
use btor::Btor;
use giputils::file::recreate_dir;
use log::info;
use rIC3::frontend::{Frontend, btor::BtorFrontend};
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
    let dut_dir = rp.path("dut");
    recreate_dir(&dut_dir)?;
    Yosys::generate_btor(&rcfg, &dut_dir)?;
    let cill_dir = rp.path("cill");
    generate_shadow(&rcfg, &cill_dir)?;
    println!(
        "CIll prepare artifacts generated in {}.",
        cill_dir.display()
    );
    dut2wts(dut_dir)?;
    Ok(())
}

pub fn dut2wts(p: PathBuf) -> anyhow::Result<()> {
    let mut btor = BtorFrontend::new(Btor::from_file(p.join("dut.btor")));
    let (mut wts, mut sym) = btor.wts();
    wts.simplify_with_symbols(&mut sym);
    let simp_btor = wts.to_btor_with_sym(&sym);
    println!("{}", simp_btor.to_string());
    // dbg!(sym.values());
    todo!()
}
