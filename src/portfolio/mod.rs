use crate::config::{EngineConfig, EngineConfigBase};
use crate::{Engine, McResult, impl_config_deref};
use clap::{Args, Parser};
use giputils::logger::with_log_level;
use log::{error, info};
use nix::errno::Errno;
use nix::sys::wait::{WaitStatus, waitpid};
use nix::unistd::Pid;
use serde::{Deserialize, Serialize};
use std::sync::mpsc::Sender;
use std::thread::{JoinHandle, spawn};
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

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct PortfolioConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    /// worker configuration
    #[arg(long = "config")]
    pub config: Option<String>,

    /// woker memory limit in GB
    #[arg(long = "worker-mem-limit", default_value_t = 16)]
    pub wmem_limit: usize,
}

impl_config_deref!(PortfolioConfig);

impl Default for PortfolioConfig {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "portfolio"]);
        cfg.into_portfolio().unwrap()
    }
}

pub struct Portfolio {
    cert: Option<PathBuf>,
    cfg: PortfolioConfig,
    engines: Vec<Worker>,
    engine_pids: Vec<Pid>,
    stop_flag: Arc<AtomicBool>,
    monitor: Option<JoinHandle<()>>,
    #[allow(unused)]
    temp_dir: TempDir,
}

struct Worker {
    name: String,
    cmd: Command,
    cert: Option<NamedTempFile>,
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
    pub fn new(model: PathBuf, cert: Option<PathBuf>, cfg: PortfolioConfig) -> Self {
        let temp_dir = tempfile::TempDir::new_in("/tmp/rIC3/").unwrap();
        let temp_dir_path = temp_dir.path();
        let mut engines = Vec::new();
        let mut id = 0;
        let mut new_engine = |name, args: &str| {
            let mut cmd = Command::new(current_exe().unwrap());
            cmd.env("RIC3_TMP_DIR", temp_dir_path);
            cmd.env("RUST_LOG", "warn");
            id += 1;
            cmd.arg("check");
            cmd.arg(&model);
            let cert = if cert.is_some() {
                let certificate = NamedTempFile::new_in(temp_dir.path()).unwrap();
                let certify_path = certificate.path().as_os_str().to_str().unwrap();
                cmd.arg("--cert");
                cmd.arg(certify_path);
                Some(certificate)
            } else {
                None
            };
            let args_split = args.split(" ");
            for a in args_split {
                cmd.arg(a);
            }
            engines.push(Worker { name, cmd, cert });
        };
        let portfolio_toml = include_str!("portfolio.toml");
        let portfolio_config: HashMap<String, HashMap<String, String>> =
            toml::from_str(portfolio_toml).unwrap();
        let config = cfg.config.as_deref().unwrap_or(match model.extension() {
            Some(ext) if (ext == "aig") | (ext == "aag") => "bl_default",
            Some(ext) if (ext == "btor") | (ext == "btor2") => "wl_default",
            _ => {
                error!("Error: unsupported file format");
                panic!();
            }
        });
        for (name, args) in portfolio_config[config].iter() {
            new_engine(name.clone(), args);
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

    pub fn check(&mut self) -> McResult {
        let mut running = HashMap::new();
        for mut engine in take(&mut self.engines) {
            let child = engine
                .cmd
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();
            info!("start engine {}", engine.name);
            let pid = Pid::from_raw(child.id() as i32);
            self.engine_pids.push(pid);
            running.insert(pid, (child, engine));
        }

        let (tx, rx) = mpsc::channel();

        self.monitor = Some(thread::spawn(move || monitor_run(tx)));

        let start = Instant::now();
        loop {
            if self.stop_flag.load(Ordering::Relaxed) {
                info!("Interrupted by external signal");
                self.terminate_inner();
                return McResult::Unknown(None);
            }

            if let Some(t) = self.cfg.time_limit
                && start.elapsed().as_secs() >= t
            {
                info!("Terminated by timeout.");
                self.terminate_inner();
                return McResult::Unknown(None);
            }

            match rx.recv_timeout(std::time::Duration::from_millis(100)) {
                Ok(msg) => match msg {
                    Some(WaitStatus::Exited(pid, code)) => {
                        if let Some((mut child, engine)) = running.remove(&pid) {
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
                                        && let Some(c) = engine.cert
                                    {
                                        let _ = std::fs::copy(c.path(), cert);
                                    }
                                    self.terminate_inner();
                                    return if r {
                                        McResult::Safe
                                    } else {
                                        McResult::Unsafe(0)
                                    };
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
                        return McResult::Unknown(None);
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

    pub fn get_stop_signal(&self) -> Arc<AtomicBool> {
        self.stop_flag.clone()
    }
}

#[derive(Default, Clone)]
pub struct LightPortfolioConfig {
    pub time_limit: Option<usize>,
}

#[derive(Default)]
pub struct LightPortfolio {
    cfg: LightPortfolioConfig,
    engines: Vec<Box<dyn Engine>>,
}

impl LightPortfolio {
    pub fn new(cfg: LightPortfolioConfig, engines: Vec<Box<dyn Engine>>) -> Self {
        Self { cfg, engines }
    }

    pub fn add_engine(&mut self, e: impl Engine + 'static) {
        self.engines.push(Box::new(e));
    }
}

impl Engine for LightPortfolio {
    fn check(&mut self) -> McResult {
        let engines = take(&mut self.engines);
        let mut stops = Vec::new();
        for e in engines.iter() {
            stops.push(e.get_stop_ctrl());
        }
        let (tx, rx) = mpsc::channel();
        let mut joins = Vec::new();
        with_log_level(log::LevelFilter::Warn, || {
            let start = Instant::now();
            let num_engines = engines.len();
            for mut e in engines {
                let tx = tx.clone();
                let join = spawn(move || {
                    let res = e.check();
                    let _ = tx.send(res);
                    res
                });
                joins.push(join);
            }
            let mut res = McResult::Unknown(None);
            let mut finished = 0;
            while finished < num_engines {
                if let Some(t) = self.cfg.time_limit
                    && start.elapsed().as_secs() >= t as u64
                {
                    info!("LightPortfolio terminated by timeout.");
                    break;
                }
                match rx.recv_timeout(std::time::Duration::from_millis(100)) {
                    Ok(r) => {
                        finished += 1;
                        if !matches!(r, McResult::Unknown(_)) {
                            res = r;
                            break;
                        }
                    }
                    Err(mpsc::RecvTimeoutError::Timeout) => continue,
                    Err(mpsc::RecvTimeoutError::Disconnected) => {
                        break;
                    }
                }
            }

            for s in stops {
                s.store(true, Ordering::Relaxed);
            }
            for j in joins {
                let _ = j.join().unwrap();
            }
            res
        })
    }
}
