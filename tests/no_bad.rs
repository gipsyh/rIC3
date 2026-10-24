use btor::Btor;
use logicrs::{Lit, fol::Term};
use rIC3::frontend::{Frontend, btor::BtorFrontend};
use std::{io::Write, process::Command};

// Issue #194: a valid BTOR2 model need not declare any bad properties.
const NO_BAD: &str = "1 sort bitvec 1
2 state 1
3 next 1 2 2
";

// Inputs, constraints, and outputs do not introduce a safety property.
const NO_BAD_WITH_CONSTRAINT: &str = "1 sort bitvec 1
2 input 1 enable
3 state 1 state
4 zero 1
5 init 1 3 4
6 xor 1 2 3
7 next 1 3 6
8 constraint 2
9 output 3
";

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
        .env("RUST_LOG", "off")
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "args={args:?}, status={}\n{stdout}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

fn check_no_bad(engine: &str) {
    for model in [NO_BAD, NO_BAD_WITH_CONSTRAINT] {
        for preproc in [true, false] {
            for cex in [true, false] {
                let mut args = Vec::new();
                if cex {
                    args.push("--cex");
                }
                // BMC cannot prove safety; bound its search for the false bad.
                args.extend([engine, "--end", "2"]);
                if !preproc {
                    args.extend(["--preproc", "false"]);
                }
                let stdout = run_cli(model, &args);
                let expected = match (engine, cex) {
                    ("bmc", true) => "UNKNOWN\n2\n",
                    ("bmc", false) => "UNKNOWN\n",
                    (_, true) => "UNSAT\n0\n",
                    (_, false) => "UNSAT\n",
                };
                assert_eq!(stdout, expected, "args={args:?}");
            }
        }
    }
}

#[test]
fn ic3_accepts_models_without_bad_properties() {
    check_no_bad("ic3");
}

#[test]
fn kind_accepts_models_without_bad_properties() {
    check_no_bad("kind");
}

#[test]
fn bmc_accepts_models_without_bad_properties() {
    check_no_bad("bmc");
}

#[test]
fn frontend_adds_false_bad_at_both_word_and_bit_levels() {
    for content in [NO_BAD, NO_BAD_WITH_CONSTRAINT] {
        let model = btor_model(content);
        let mut frontend = BtorFrontend::new(Btor::from_file(model.path()));
        let (wts, symbols) = frontend.wts();
        assert_eq!(wts.bad, vec![Term::bool_const(false)]);
        assert_eq!(symbols.prop, vec![String::new()]);
        let (ts, _) = frontend.ts();
        assert_eq!(ts.bad.as_slice(), &[Lit::FALSE]);
    }
}

#[test]
fn frontend_preserves_existing_bad_properties_and_labels() {
    let model = btor_model(&format!(
        "{NO_BAD_WITH_CONSTRAINT}10 bad 2 enabled\n11 bad 3 active\n"
    ));
    let btor = Btor::from_file(model.path());
    let (wts, symbols) = BtorFrontend::new(btor.clone()).wts();
    assert_eq!(wts.bad, btor.bad);
    assert_eq!(symbols.prop, btor.prop_label);
}

#[test]
fn no_bad_writes_a_proof() {
    for engine in ["ic3", "kind"] {
        let dir = tempfile::tempdir().unwrap();
        let cert = dir.path().join("safe.btor2");
        let stdout = run_cli(
            NO_BAD_WITH_CONSTRAINT,
            &["--cert", cert.to_str().unwrap(), engine, "--end", "2"],
        );
        assert_eq!(stdout, "UNSAT\n");
        let proof = Btor::from_file(&cert);
        assert_eq!(proof.bad.len(), 1);
        let stdout = run_cli(
            &std::fs::read_to_string(&cert).unwrap(),
            &["ic3", "--end", "5"],
        );
        assert_eq!(stdout, "UNSAT\n");
    }
}
