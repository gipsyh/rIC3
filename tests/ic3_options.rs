use std::{io::Write, process::Command};

/// 4-bit counter from zero; bad when equal to 9, i.e. at depth 9.
const COUNTER: &str = "1 sort bitvec 4
2 sort bitvec 1
3 state 1 counter
4 zero 1
5 one 1
6 constd 1 9
7 init 1 3 4
8 add 1 3 5
9 next 1 3 8
10 eq 2 3 6
11 bad 10
";

fn run_cli(args: &[&str]) -> (bool, String, String) {
    let mut model = tempfile::Builder::new()
        .suffix(".btor2")
        .tempfile()
        .unwrap();
    model.write_all(COUNTER.as_bytes()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ric3"))
        .arg("check")
        .arg(model.path())
        .args(["--ui", "false"])
        .args(args)
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// `--dynamic` and `--mab` are incompatible with dropping proof obligations, which is on by
/// default: they turn it off unless `--drop-po` is given explicitly.
#[test]
fn dynamic_and_mab_imply_no_drop_po() {
    for args in [["ic3", "--dynamic"], ["ic3", "--mab"]] {
        let (ok, stdout, stderr) = run_cli(&args);
        assert!(ok && stdout.contains("SAT"), "{args:?}\n{stdout}\n{stderr}");
    }
}

#[test]
fn explicit_drop_po_with_dynamic_is_still_rejected() {
    let (ok, stdout, stderr) = run_cli(&["ic3", "--dynamic", "--drop-po=true"]);
    assert!(
        !ok && (stdout + &stderr).contains("cannot enable both dynamic and drop-po"),
        "{stderr}"
    );
}
