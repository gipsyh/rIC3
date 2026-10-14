use std::{io::Write, process::Command};

fn btor_model(content: &str) -> tempfile::NamedTempFile {
    let mut model = tempfile::Builder::new()
        .suffix(".btor2")
        .tempfile()
        .unwrap();
    model.write_all(content.as_bytes()).unwrap();
    model
}

fn run_cli(content: &str, args: &[&str]) -> String {
    let model = btor_model(content);
    let output = Command::new(env!("CARGO_BIN_EXE_ric3"))
        .arg("check")
        .arg(model.path())
        .args(["--ui", "false"])
        .args(args)
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

/// Counter `x` (4 bits, free increment); bad when `x * 3 != (x << 1) + x`. The property holds,
/// but the uninterpreted-function abstraction of `mul` admits a spurious counterexample.
const MUL_SHIFT_ADD: &str = "1 sort bitvec 4
2 sort bitvec 1
3 state 1 x
4 input 1 a
5 constd 1 3
6 mul 1 3 5
7 constd 1 1
8 sll 1 3 7
9 add 1 8 3
10 neq 2 6 9
11 bad 10
12 zero 1
13 init 1 3 12
14 add 1 3 4
15 next 1 3 14
";

/// Same counter; bad when `x * 3 == 9`, reachable at depth 3 (`x = 3`).
const MUL_REACHABLE: &str = "1 sort bitvec 4
2 sort bitvec 1
3 state 1 x
4 input 1 a
5 constd 1 3
6 mul 1 3 5
7 constd 1 9
8 eq 2 6 7
9 bad 8
10 zero 1
11 init 1 3 10
12 add 1 3 4
13 next 1 3 12
";

#[test]
fn cegar_falls_back_to_the_concrete_model_on_a_spurious_counterexample() {
    let stdout = run_cli(MUL_SHIFT_ADD, &["cegar"]);
    assert!(stdout.contains("UNSAT"), "{stdout}");
}

#[test]
fn cegar_reports_a_real_counterexample_after_the_fallback() {
    let stdout = run_cli(MUL_REACHABLE, &["--cex", "cegar"]);
    assert!(
        stdout.contains("SAT") && !stdout.contains("UNSAT"),
        "{stdout}"
    );
    assert!(stdout.contains("#0") && stdout.contains("@1"), "{stdout}");
}

#[test]
fn cegar_writes_a_proof_after_the_fallback() {
    let model = btor_model(MUL_SHIFT_ADD);
    let cert = tempfile::Builder::new()
        .suffix(".btor2")
        .tempfile()
        .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ric3"))
        .arg("check")
        .arg(model.path())
        .args(["--ui", "false", "--cert"])
        .arg(cert.path())
        .arg("cegar")
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success() && stdout.contains("UNSAT"),
        "{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!std::fs::read_to_string(cert.path()).unwrap().is_empty());
}
