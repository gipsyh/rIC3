use std::{fs, path::Path, process::Command};

// https://github.com/gipsyh/rIC3/issues/197
// Run the original reproducer with:
// cargo test --release --test btor_certificate -- --ignored
#[test]
#[ignore = "slow: IC3 must learn the 256-bit one-hot invariant"]
fn onehot_ic3_writes_large_certificate() {
    let model = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/btor_certificate/test.btor");
    let dir = tempfile::tempdir().unwrap();
    let cert = dir.path().join("proof.btor2");
    let output = Command::new(env!("CARGO_BIN_EXE_ric3"))
        .arg("check")
        .arg(model)
        .args(["--cex", "--ui", "false", "--cert"])
        .arg(&cert)
        .args(["ic3", "--time-limit", "300"])
        .env("RUST_LOG", "off")
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "status={}\n{stdout}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(stdout, "UNSAT\n0\n");
    let proof = fs::read_to_string(cert).unwrap();
    assert!(
        proof
            .lines()
            .any(|line| { line.split_whitespace().nth(1) == Some("bad") })
    );
}
