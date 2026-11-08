use std::{path::Path, process::Command, sync::OnceLock};

fn certify_available(model: &Path) -> bool {
    static AIG: OnceLock<bool> = OnceLock::new();
    static BTOR: OnceLock<bool> = OnceLock::new();
    let (image, available) = match model.extension().and_then(|ext| ext.to_str()).unwrap() {
        "aig" | "aag" => ("ghcr.io/gipsyh/certifaiger:latest", &AIG),
        "btor" | "btor2" => ("ghcr.io/gipsyh/cerbtora:latest", &BTOR),
        ext => panic!("unsupported model extension: {ext}"),
    };
    *available.get_or_init(|| {
        // Check the daemon as well as the CLI; Docker may be installed but stopped.
        let available = Command::new("docker")
            .arg("info")
            .output()
            .is_ok_and(|output| output.status.success())
            && Command::new("docker")
                .args(["image", "inspect", image])
                .output()
                .is_ok_and(|output| output.status.success());
        if !available {
            eprintln!("Docker or {image} unavailable; checking results without --certify");
        }
        available
    })
}

pub fn check(model: &Path, args: &[&str], expected: &str) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ric3"));
    command.arg("check").arg(model).args(["--ui", "false"]);
    if certify_available(model) {
        command.arg("--certify");
    }
    let output = command
        .args(args)
        .args(["--time-limit", "60"])
        .env("RUST_LOG", "off")
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let context = format!(
        "model={}, args={args:?}, status={}\n{stdout}\n{stderr}",
        model.display(),
        output.status
    );
    // Certificate failures and crashes must still fail when a result was printed.
    assert!(output.status.success(), "{context}");
    let results: Vec<_> = stdout
        .lines()
        .filter(|line| matches!(*line, "SAT" | "UNSAT" | "UNKNOWN"))
        .collect();
    assert_eq!(results, [expected], "{context}");
}
