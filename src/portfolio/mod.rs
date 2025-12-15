use crate::EngineConfig;
use log::{error, info};
use nix::errno::Errno;
use nix::sys::wait::{WaitStatus, waitpid};
use nix::unistd::Pid;
use std::sync::mpsc::Sender;
use std::thread::JoinHandle;
use std::time::Instant;
use std::{
    collections::HashMap,
    env::current_exe,
    io::{BufRead, BufReader, Read},
    mem::take,
    path::PathBuf,
    process::{Command, Stdio},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread,
};
use tempfile::{NamedTempFile, TempDir};

pub struct Portfolio {
    cert: Option<PathBuf>,
    #[allow(unused)]
    cfg: EngineConfig,
    engines: Vec<Engine>,
    temp_dir: TempDir,
    engine_pids: Vec<Pid>,
    stop_flag: Arc<AtomicBool>,
    monitor: Option<JoinHandle<()>>,
}

struct Engine {
    name: String,
    cmd: Command,
}

fn monitor_run(tx: Sender<Option<WaitStatus>>) {
    loop {
        match waitpid(None, None) {
            Ok(status) => {
                tx.send(Some(status)).unwrap();
            }
            Err(Errno::EINTR) => continue,
            Err(_) => break,
        }
    }
    tx.send(None).unwrap();
}

impl Portfolio {
    pub fn new(model: PathBuf, cert: Option<PathBuf>, cfg: EngineConfig) -> Self {
        let temp_dir = tempfile::TempDir::new_in("/tmp/rIC3/").unwrap();
        let temp_dir_path = temp_dir.path();
        let mut engines = Vec::new();
        let mut id = 0;
        let mut new_engine = |name, args: &str| {
            let args_split = args.split(" ");
            let mut cmd = Command::new(current_exe().unwrap());
            cmd.env("RIC3_TMP_DIR", temp_dir_path);
            cmd.env("RUST_LOG", "warn");
            id += 1;
            cmd.arg("check");
            cmd.arg(&model);
            for a in args_split {
                cmd.arg(a);
            }
            engines.push(Engine { name, cmd });
        };
        let portfolio_toml = include_str!("portfolio.toml");
        let portfolio_config: HashMap<String, HashMap<String, String>> =
            toml::from_str(portfolio_toml).unwrap();
        let portfolio_config = match model.extension() {
            Some(ext) if (ext == "aig") | (ext == "aag") => portfolio_config["bl_default"].clone(),
            Some(ext) if (ext == "btor") | (ext == "btor2") => {
                portfolio_config["wl_default"].clone()
            }
            _ => {
                error!("Error: unsupported file format");
                panic!();
            }
        };
        for (name, args) in portfolio_config {
            new_engine(name, &args);
        }
        Self {
            cert,
            cfg,
            engines,
            temp_dir,
            engine_pids: Default::default(),
            stop_flag: Arc::new(AtomicBool::new(false)),
            monitor: None,
        }
    }

    fn terminate_inner(&mut self) {
        for pid in self.engine_pids.iter() {
            let _ = nix::sys::signal::kill(*pid, nix::sys::signal::Signal::SIGTERM);
        }
        take(&mut self.monitor).unwrap().join().unwrap();
    }

    pub fn check(&mut self) -> Option<bool> {
        let mut running = HashMap::new();
        for mut engine in take(&mut self.engines) {
            let certificate = if self.cert.is_some() {
                let certificate = NamedTempFile::new_in(self.temp_dir.path()).unwrap();
                let certify_path = certificate.path().as_os_str().to_str().unwrap();
                engine.cmd.arg(certify_path);
                Some(certificate)
            } else {
                None
            };

            let child = engine
                .cmd
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();

            info!("start engine {}", engine.name);

            let pid = Pid::from_raw(child.id() as i32);
            self.engine_pids.push(pid);
            running.insert(pid, (child, engine, certificate));
        }

        let (tx, rx) = mpsc::channel();

        self.monitor = Some(thread::spawn(move || monitor_run(tx)));

        let start = Instant::now();
        loop {
            if self.stop_flag.load(Ordering::Relaxed) {
                info!("Interrupted by external signal");
                self.terminate_inner();
                return None;
            }

            if let Some(t) = self.cfg.time_limit
                && start.elapsed().as_secs() >= t
            {
                info!("Terminated by timeout.");
                self.terminate_inner();
                return None;
            }

            match rx.recv_timeout(std::time::Duration::from_millis(100)) {
                Ok(msg) => match msg {
                    Some(WaitStatus::Exited(pid, code)) => {
                        if let Some((mut child, engine, certificate)) = running.remove(&pid) {
                            if code == 0 {
                                let stdout = child.stdout.take().unwrap();
                                let reader = BufReader::new(stdout);
                                let mut res = None;
                                for l in reader.lines().map_while(Result::ok) {
                                    match l.as_str() {
                                        "SAT" => res = Some(false),
                                        "UNSAT" => res = Some(true),
                                        _ => (),
                                    }
                                }

                                if let Some(r) = res {
                                    let config = engine
                                        .cmd
                                        .get_args()
                                        .skip(1)
                                        .map(|s| s.to_str().unwrap())
                                        .collect::<Vec<_>>()
                                        .join(" ");
                                    info!("best configuration: {config}");
                                    if let Some(cert) = &self.cert
                                        && let Some(c) = certificate
                                    {
                                        let _ = std::fs::copy(c.path(), cert);
                                    }
                                    self.terminate_inner();
                                    return Some(r);
                                }
                            } else {
                                let mut stderr = String::new();
                                if let Some(mut e) = child.stderr.take() {
                                    let _ = e.read_to_string(&mut stderr);
                                }
                                info!("{} exited with code {}: {}", engine.name, code, stderr);
                            }
                        }
                    }
                    Some(WaitStatus::Signaled(pid, _, _)) => {
                        running.remove(&pid);
                    }
                    None => {
                        error!("all workers unexpectedly exited :(");
                        self.terminate_inner();
                        return None;
                    }
                    _ => unreachable!(),
                },
                Err(mpsc::RecvTimeoutError::Timeout) => continue,
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    error!("monitor thread disconnected");
                    unreachable!();
                }
            }
        }
    }
}
