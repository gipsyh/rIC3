use nix::{
    sys::signal::{Signal, killpg},
    unistd::Pid,
};
use std::{
    io::{BufRead, BufReader, Read},
    os::unix::process::CommandExt,
    path::Path,
    process::{Command, Stdio},
    sync::OnceLock,
    thread,
    time::{Duration, Instant},
};

const TIMEOUT: Duration = Duration::from_secs(1000);

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

fn capture_output(reader: impl Read + Send + 'static, stderr: bool) -> thread::JoinHandle<Vec<u8>> {
    thread::spawn(move || {
        let mut reader = BufReader::new(reader);
        let mut output = Vec::new();
        let mut line = Vec::new();
        while reader.read_until(b'\n', &mut line).unwrap() != 0 {
            let text = String::from_utf8_lossy(&line);
            if stderr {
                eprint!("{text}");
            } else {
                print!("{text}");
            }
            output.extend_from_slice(&line);
            line.clear();
        }
        output
    })
}

pub fn check(model: &Path, args: &[&str], expected: &str, certify: bool) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ric3"));
    command.arg("check").arg(model).args(["--ui", "false"]);
    if certify && certify_available(model) {
        command.arg("--certify");
    }
    if std::env::var_os("RUST_LOG").is_none() {
        command.env("RUST_LOG", "off");
    }
    let timeout_seconds = TIMEOUT.as_secs().to_string();
    command
        .args(args)
        .args(["--time-limit", &timeout_seconds])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0);
    let start = Instant::now();
    let mut child = command.spawn().unwrap();
    // Drain both pipes concurrently, displaying output live with --nocapture
    // while retaining it for result checks and timeout diagnostics.
    let stdout = capture_output(child.stdout.take().unwrap(), false);
    let stderr = capture_output(child.stderr.take().unwrap(), true);
    let (status, timed_out) = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break (status, false);
        }
        if start.elapsed() >= TIMEOUT {
            // The engine's time limit cannot interrupt preprocessing. Kill the
            // process group as well, so forked workers do not outlive the test.
            let _ = killpg(Pid::from_raw(child.id() as i32), Signal::SIGKILL);
            let _ = child.kill();
            break (child.wait().unwrap(), true);
        }
        thread::sleep(Duration::from_millis(10));
    };
    let stdout_bytes = stdout.join().unwrap();
    let stderr_bytes = stderr.join().unwrap();
    let stdout = String::from_utf8_lossy(&stdout_bytes);
    let stderr = String::from_utf8_lossy(&stderr_bytes);
    let context = format!(
        "model={}, args={args:?}, status={status}\n{stdout}\n{stderr}",
        model.display(),
    );
    assert!(!timed_out, "timed out after {timeout_seconds}s\n{context}");
    // Certificate failures and crashes must still fail when a result was printed.
    assert!(status.success(), "{context}");
    let results: Vec<_> = stdout
        .lines()
        .filter(|line| matches!(*line, "SAT" | "UNSAT" | "UNKNOWN"))
        .collect();
    assert_eq!(results, [expected], "{context}");
}
