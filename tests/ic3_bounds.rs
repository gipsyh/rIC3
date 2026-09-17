use std::{io::Write, process::Command};

/// 8-bit counter from zero; bad when equal to `bad`, i.e. at depth `bad`.
fn counter_model(bad: u8) -> tempfile::NamedTempFile {
    let mut model = tempfile::Builder::new()
        .suffix(".btor2")
        .tempfile()
        .unwrap();
    write!(
        model,
        "1 sort bitvec 8
2 sort bitvec 1
3 state 1 counter
4 zero 1
5 one 1
6 constd 1 {bad}
7 init 1 3 4
8 add 1 3 5
9 next 1 3 8
10 eq 2 3 6
11 bad 10
"
    )
    .unwrap();
    model
}

fn run_cli(bad: u8, args: &[&str]) -> String {
    let model = counter_model(bad);
    let output = Command::new(env!("CARGO_BIN_EXE_ric3"))
        .arg("check")
        .arg(model.path())
        .args(["--ui", "false"])
        .args(args)
        .env("RUST_LOG", "info")
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

#[test]
fn ic3_reports_reached_bound_without_proof() {
    let stdout = run_cli(3, &["ic3", "--end", "2"]);
    assert!(stdout.ends_with("UNKNOWN\n"), "{stdout}");
    assert!(
        stdout.contains("IC3 reached bound 2, stopping search"),
        "{stdout}"
    );
    assert!(!stdout.contains("proved the property"), "{stdout}");
    let progress: Vec<_> = stdout
        .lines()
        .filter_map(|line| line.split_once("IC3 found no counterexample "))
        .map(|(_, rest)| rest)
        .collect();
    assert_eq!(
        progress,
        ["up to depth 0", "up to depth 1", "up to depth 2"],
        "{stdout}"
    );
}

#[test]
fn ic3_keeps_counterexamples_found_beyond_the_bound() {
    // Obligations may hit a counterexample deeper than --end before the bound completes.
    let stdout = run_cli(127, &["--cex", "ic3", "--end", "99"]);
    assert!(
        stdout.contains("IC3 found a counterexample at depth 127"),
        "{stdout}"
    );
    assert!(stdout.contains("\nSAT\n"), "{stdout}");
    assert!(!stdout.contains("reached bound"), "{stdout}");
}

#[test]
fn ic3_time_limit_zero_completes_no_depth() {
    let stdout = run_cli(0, &["ic3", "--end", "0", "--time-limit", "0"]);
    assert!(stdout.ends_with("UNKNOWN\n"), "{stdout}");
    assert!(!stdout.contains("found no counterexample"), "{stdout}");
}

#[test]
fn unknown_does_not_request_a_certificate() {
    for engine_args in [&["ic3", "--end", "2"], &["bmc", "--end", "2"]] {
        let run = |prefix: &[&str]| run_cli(3, &[prefix, engine_args].concat());
        // With --cex, UNKNOWN prints "2" in place of a witness.
        for (option, expected) in [("--cex", "UNKNOWN\n2\n"), ("--certify", "UNKNOWN\n")] {
            let stdout = run(&[option]);
            assert!(stdout.ends_with(expected), "{stdout}");
        }
        let dir = tempfile::tempdir().unwrap();
        let cert = dir.path().join("bounded.cert");
        let stdout = run(&["--cert", cert.to_str().unwrap()]);
        assert!(stdout.ends_with("UNKNOWN\n"), "{stdout}");
        assert!(!cert.exists(), "UNKNOWN must not create a certificate");
    }
}
