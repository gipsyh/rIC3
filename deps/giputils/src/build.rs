use std::{
    env,
    fs::remove_dir_all,
    io,
    path::{Path, PathBuf},
    process::Command,
};

/// Links the target's default C++ runtime unless CXXSTDLIB overrides it.
/// An empty CXXSTDLIB leaves runtime selection to the linker driver.
pub fn link_cxx_stdlib() {
    println!("cargo:rerun-if-env-changed=CXXSTDLIB");
    let lib = env::var("CXXSTDLIB").unwrap_or_else(|_| {
        match env::var("CARGO_CFG_TARGET_OS").as_deref() {
            Ok("linux") => "stdc++".into(),
            Ok("macos") => "c++".into(),
            _ => String::new(),
        }
    });
    if !lib.is_empty() {
        println!("cargo:rustc-link-lib=dylib={lib}");
    }
}

pub fn copy_build(src: &str, f: impl FnOnce(&Path) -> io::Result<()>) -> io::Result<PathBuf> {
    let src_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join(src);
    let cp_dir = PathBuf::from(env::var("OUT_DIR").unwrap()).join(src);
    if cp_dir.exists() {
        remove_dir_all(&cp_dir).unwrap();
    }
    Command::new("cp")
        .arg("-r")
        .arg(src_dir.as_path())
        .arg(&cp_dir)
        .status()?;
    f(&cp_dir)?;
    Ok(cp_dir)
}

pub fn git_submodule_update() -> io::Result<()> {
    git_submodule_update_in(&env::current_dir()?)
}

fn git_submodule_update_in(dir: &Path) -> io::Result<()> {
    // Workspace crates share the repository root; packaged sources may have no Git metadata.
    if !dir.ancestors().any(|parent| parent.join(".git").exists()) {
        return Ok(());
    }
    // Only initialize this crate's sources, not other workspace members or benchmarks.
    let output = Command::new("git")
        .args(["submodule", "status", "--", "."])
        .current_dir(dir)
        .output()?;
    if !output.status.success() {
        return Err(io::Error::other(format!(
            "git exited with {}",
            output.status
        )));
    }

    let need_init: Vec<String> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            line.strip_prefix('-')?;
            line.split_whitespace().nth(1).map(str::to_owned)
        })
        .collect();

    if need_init.is_empty() {
        return Ok(());
    }

    let status = Command::new("git")
        .args(["submodule", "update", "--init", "--"])
        .args(&need_init)
        .current_dir(dir)
        .status()?;

    if !status.success() {
        return Err(io::Error::other(format!(
            "`git submodule update --init` failed with {status}"
        )));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn git(dir: &Path, args: &[&str]) {
        let output = Command::new("git")
            .args([
                "-c",
                "user.name=Build test",
                "-c",
                "user.email=build-test@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                "protocol.file.allow=always",
            ])
            .args(args)
            .current_dir(dir)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn packaged_sources_do_not_need_a_git_repository() {
        let package = tempfile::tempdir().unwrap();
        fs::create_dir(package.path().join("native")).unwrap();
        git_submodule_update_in(package.path()).unwrap();
    }

    #[test]
    fn workspace_crate_initializes_only_its_own_submodules() {
        let temp = tempfile::tempdir().unwrap();
        let source = temp.path().join("source");
        let repo = temp.path().join("repo");
        fs::create_dir(&source).unwrap();
        fs::create_dir(&repo).unwrap();
        git(&source, &["init", "--quiet"]);
        fs::write(source.join("native.txt"), "original").unwrap();
        git(&source, &["add", "native.txt"]);
        git(&source, &["commit", "--quiet", "-m", "fixture"]);
        git(&repo, &["init", "--quiet"]);
        for path in ["crates/solver/native", "crates/other/native"] {
            git(
                &repo,
                &[
                    "submodule",
                    "add",
                    "--quiet",
                    source.to_str().unwrap(),
                    path,
                ],
            );
        }
        // Keep the cached repositories so the build helper needs no network access.
        git(&repo, &["submodule", "deinit", "--force", "--all"]);
        let solver = repo.join("crates/solver");
        let native_file = solver.join("native/native.txt");
        assert!(!native_file.exists());

        git_submodule_update_in(&solver).unwrap();
        assert_eq!(fs::read_to_string(&native_file).unwrap(), "original");
        assert!(!repo.join("crates/other/native/.git").exists());

        fs::write(&native_file, "local changes").unwrap();
        git_submodule_update_in(&solver).unwrap();
        assert_eq!(fs::read_to_string(&native_file).unwrap(), "local changes");
    }
}
