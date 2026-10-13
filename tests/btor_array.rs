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

/// Array state `initmem` without init and next is the base of the init of `mem`
/// (yosys emits this for memories with non-uniform init data).
const ARRAY_WRITE_CHAIN_INIT: &str = "1 sort bitvec 2
2 sort bitvec 4
3 sort array 1 2
4 sort bitvec 1
5 input 1 idx
6 input 2 val
7 state 3 initmem
8 constd 1 2
9 constd 2 3
10 write 3 7 8 9
11 state 3 mem
12 init 3 11 10
13 write 3 11 5 6
14 next 3 11 13
15 one 1
16 read 2 11 15
17 constd 2 5
18 eq 4 16 17
19 bad 18
";

const ARRAY_INPUT: &str = "1 sort bitvec 2
2 sort bitvec 4
3 sort array 1 2
4 sort bitvec 1
5 input 3 arr
6 one 1
7 read 2 5 6
8 constd 2 5
9 eq 4 7 8
10 bad 9
";

#[test]
fn array_state_without_next_is_restored_in_the_witness() {
    let stdout = run_cli(ARRAY_WRITE_CHAIN_INIT, &["--cex", "ic3"]);
    assert!(stdout.contains("\nSAT\n"), "{stdout}");
    // mem = write(initmem, 2, 3) in frame 0 and read(mem, 1) == 5 is the bad
    assert!(stdout.contains("\n1 [01] 0101\n1 [10] 0011\n"), "{stdout}");
    assert!(stdout.trim_end().ends_with("\n."), "{stdout}");
}

#[test]
fn array_input_is_restored_in_the_witness() {
    let stdout = run_cli(ARRAY_INPUT, &["--cex", "ic3"]);
    assert!(stdout.contains("\nSAT\n"), "{stdout}");
    assert!(stdout.contains("\n@0\n0 [00] "), "{stdout}");
    assert!(stdout.contains("\n0 [01] 0101\n"), "{stdout}");
    assert!(stdout.trim_end().ends_with("\n."), "{stdout}");
}
