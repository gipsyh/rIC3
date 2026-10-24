use giputils::build::copy_build;
use std::process::Command;
use std::{env, io};
extern crate giputils;

fn main() -> io::Result<()> {
    for var in ["CC", "CFLAGS"] {
        println!("cargo:rerun-if-env-changed={var}");
    }
    giputils::build::git_submodule_update()?;
    println!("cargo:rerun-if-changed=./kissat");
    let cb_path = copy_build("kissat", |src| {
        let mut cc = env::var_os("CC").unwrap_or_else(|| "clang".into());
        // Kissat's configure resets CFLAGS and embeds its own flags in CC.
        // Include the caller's flags in CC so they also reach the linker.
        if let Some(cflags) = env::var_os("CFLAGS") {
            cc.push(" ");
            cc.push(cflags);
        }
        let status = Command::new("sh")
            .env("CC", cc)
            .arg("configure")
            .arg("-fPIC")
            .arg("--competition")
            .current_dir(src)
            .status()?;
        if !status.success() {
            return Err(io::Error::other(format!(
                "configure failed with status: {}",
                status
            )));
        }
        let num_jobs = env::var("NUM_JOBS").unwrap();
        let status = Command::new("make")
            .arg(format!("-j{num_jobs}"))
            .current_dir(src)
            .status()?;
        if !status.success() {
            return Err(io::Error::other(format!(
                "make failed with status: {}",
                status
            )));
        }
        Ok(())
    })?;
    println!(
        "cargo:rustc-link-search=native={}",
        cb_path.join("build").display()
    );
    println!("cargo:rustc-link-lib=static=kissat");
    Ok(())
}
