use cmake::Config;
use giputils::build::{copy_build, link_cxx_stdlib};
use std::path::PathBuf;
use std::process::Command;
use std::{env, io};

fn main() -> io::Result<()> {
    for var in ["CXX", "CXXFLAGS"] {
        println!("cargo:rerun-if-env-changed={var}");
    }
    giputils::build::git_submodule_update()?;
    let out_dir = env::var("OUT_DIR").unwrap();

    let bindings = PathBuf::from("./bindings");
    println!("cargo:rerun-if-changed=./bindings");
    Config::new(bindings).build();

    println!("cargo:rerun-if-changed=./cadical");
    let cb_path = copy_build("cadical", |src| {
        let status = Command::new("sh")
            .arg("configure")
            .arg("-fPIC")
            .env(
                "CXX",
                env::var_os("CXX").unwrap_or_else(|| "clang++".into()),
            )
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
    println!(
        "cargo:rustc-link-search=native={}",
        PathBuf::from(out_dir).join("lib").display()
    );
    println!("cargo:rustc-link-lib=static=cadical");
    println!("cargo:rustc-link-lib=static=bindings");
    link_cxx_stdlib();
    Ok(())
}
