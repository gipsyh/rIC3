use std::{path::Path, process::Command};

// https://github.com/gipsyh/rIC3/issues/192
// test.btor reconstructs the 14-line SAT example described in the issue.
// Run with: cargo test --test scorr_init -- --nocapture
#[test]
fn bmc_counterexample_does_not_panic_after_scorr() {
    let model = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/scorr_init/test.btor");
    let output = Command::new(env!("CARGO_BIN_EXE_ric3"))
        .arg("check")
        .arg(model)
        .args([
            "--cex",
            "--ui",
            "false",
            "bmc",
            "--end",
            "3",
            "--time-limit",
            "10",
        ])
        .env("RUST_LOG", "off")
        .env("RUST_BACKTRACE", "1")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "status={}\n{}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
