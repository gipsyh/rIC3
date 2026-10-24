extern crate giputils;
#[cfg(feature = "vendor")]
use giputils::build::copy_build;
use giputils::build::link_cxx_stdlib;
use std::io;
#[cfg(feature = "vendor")]
use std::process::Command;

#[cfg(feature = "vendor")]
fn build_vendor() -> io::Result<()> {
    giputils::build::git_submodule_update()?;
    println!("cargo:rerun-if-changed=./bitwuzla");
    let cb_path = copy_build("bitwuzla", |src| {
        let status = Command::new("python3")
            .arg("configure.py")
            .current_dir(src)
            .status()?;
        if !status.success() {
            return Err(io::Error::other(format!(
                "configure.py failed with status: {}",
                status
            )));
        }
        let status = Command::new("meson")
            .arg("compile")
            .current_dir(src.join("build"))
            .status()?;
        if !status.success() {
            return Err(io::Error::other(format!(
                "meson compile failed with status: {}",
                status
            )));
        }
        Ok(())
    })?;
    println!(
        "cargo:rustc-link-search=native={}",
        cb_path.join("build").join("src").display()
    );
    println!(
        "cargo:rustc-link-search=native={}",
        cb_path.join("build").join("src").join("lib").display()
    );
    println!("cargo:rustc-link-lib=static=bitwuzla");
    println!("cargo:rustc-link-lib=static=bzlautil");
    println!("cargo:rustc-link-lib=static=bitwuzlabb");
    println!("cargo:rustc-link-lib=static=bitwuzlabv");
    println!("cargo:rustc-link-lib=static=bitwuzlals");
    println!("cargo:rustc-link-lib=static=bzlarng");
    link_cxx_stdlib();
    println!("cargo:rustc-link-lib=dylib=gmp");
    println!("cargo:rustc-link-lib=dylib=mpfr");
    Ok(())
}

#[cfg(not(feature = "vendor"))]
fn link_system() -> io::Result<()> {
    if let Ok(lib) = pkg_config::Config::new().probe("bitwuzla") {
        for path in lib.link_paths {
            println!("cargo:rustc-link-arg=-Wl,-rpath,{}", path.display());
        }
        for lib in lib.libs {
            println!("cargo:rustc-link-lib=dylib={}", lib);
        }
        link_cxx_stdlib();
    } else {
        println!(
            "cargo:warning=Bitwuzla not found. The library will panic at runtime if used. Please install it from https://github.com/bitwuzla/bitwuzla"
        );
        println!("cargo:rustc-cfg=bitwuzla_stub");
    }
    Ok(())
}

fn main() -> io::Result<()> {
    // Declare bitwuzla_stub as a valid cfg
    println!("cargo::rustc-check-cfg=cfg(bitwuzla_stub)");

    #[cfg(feature = "vendor")]
    build_vendor()?;

    #[cfg(not(feature = "vendor"))]
    link_system()?;

    Ok(())
}
