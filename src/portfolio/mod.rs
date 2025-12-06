use crate::{Config, frontend::aig::certifaiger_check};
use log::{error, info};
use process_control::{ChildExt, Control};
use serde::Deserialize;
use std::{
    collections::HashMap,
    env::current_exe,
    fs::File,
    io::{Read, Write},
    mem::take,
    ops::{Deref, DerefMut},
    process::{Command, Stdio, exit},
    sync::{Arc, Condvar, Mutex},
    thread::spawn,
};
use tempfile::{NamedTempFile, TempDir};

enum PortfolioState {
    Checking(usize),
    Finished(bool, String, Option<NamedTempFile>),
    Terminate,
}

impl PortfolioState {
    fn new(nt: usize) -> Self {
        PortfolioState::Checking(nt)
    }
}

impl PortfolioState {
    fn is_checking(&self) -> bool {
        matches!(self, Self::Checking(_))
    }

    fn result(&mut self) -> (bool, String, Option<NamedTempFile>) {
        let Self::Finished(res, config, certificate) = self else {
            panic!()
        };
        (*res, config.clone(), take(certificate))
    }
}

pub struct Portfolio {
    cfg: Config,
    engines: Vec<Engine>,
    temp_dir: TempDir,
    engine_pids: Vec<i32>,
    certificate: Option<NamedTempFile>,
    state: Arc<(Mutex<PortfolioState>, Condvar)>,
}

struct Engine {
    name: String,
    cmd: Command,
}

#[derive(Deserialize)]
struct PortfolioConfig {
    engine: HashMap<String, String>,
}

impl Portfolio {
    pub fn new(cfg: Config) -> Self {
        let temp_dir = tempfile::TempDir::new_in("/tmp/rIC3/").unwrap();
        let temp_dir_path = temp_dir.path();
        let mut engines = Vec::new();
        let mut id = 0;
        let mut new_engine = |name, args: &str| {
            let args_split = args.split(" ");
            let mut cmd = Command::new(current_exe().unwrap());
            cmd.env("RIC3_TMP_DIR", temp_dir_path);
            cmd.env("RUST_LOG", "warn");
            cmd.env("RIC3_WORKER", format!("worker{id}"));
            id += 1;
            cmd.arg(&cfg.model);
            for a in args_split {
                cmd.arg(a);
            }
            engines.push(Engine { name, cmd });
        };
        let portfolio_toml = include_str!("portfolio.toml");
        let portfolio_config: PortfolioConfig = toml::from_str(portfolio_toml).unwrap();
        for (name, args) in portfolio_config.engine {
            new_engine(name, &args);
        }
        let ps = PortfolioState::new(engines.len());
        Self {
            cfg,
            engines,
            temp_dir,
            certificate: None,
            engine_pids: Default::default(),
            state: Arc::new((Mutex::new(ps), Condvar::new())),
        }
    }

    pub fn terminate(&mut self) {
        let Ok(mut lock) = self.state.0.try_lock() else {
            return;
        };
        if lock.is_checking() {
            *lock = PortfolioState::Terminate;
            let pids: Vec<String> = self.engine_pids.iter().map(|p| format!("{}", *p)).collect();
            let pid = pids.join(",");
            let _ = Command::new("pkill")
                .args(["-9", "--parent", &pid])
                .output();
            let mut kill = Command::new("kill");
            kill.arg("-9");
            for p in pids {
                kill.arg(p);
            }
            let _ = kill.output().unwrap();
            self.engine_pids.clear();
            let _ = Command::new("rm")
                .arg("-rf")
                .arg(self.temp_dir.path())
                .output();
        }
        drop(lock);
    }

    fn check_inner(&mut self) -> Option<bool> {
        #[cfg(target_os = "linux")]
        let wmem = self.cfg.portfolio.wmem_limit * 1024 * 1024 * 1024;
        let lock = self.state.0.lock().unwrap();
        for mut engine in take(&mut self.engines) {
            let certificate =
                if self.cfg.certificate.is_some() || self.cfg.certify || self.cfg.witness {
                    let certificate =
                        tempfile::NamedTempFile::new_in(self.temp_dir.path()).unwrap();
                    let certify_path = certificate.path().as_os_str().to_str().unwrap();
                    engine.cmd.arg(certify_path);
                    Some(certificate)
                } else {
                    None
                };
            let mut child = engine.cmd.stderr(Stdio::piped()).spawn().unwrap();
            self.engine_pids.push(child.id() as i32);
            let state = self.state.clone();
            spawn(move || {
                let config = engine
                    .cmd
                    .get_args()
                    .skip(1)
                    .map(|cstr| cstr.to_str().unwrap())
                    .collect::<Vec<&str>>();
                let config = config.join(" ");
                info!("start engine {}: {config}", engine.name);
                #[cfg(target_os = "linux")]
                let status = child
                    .controlled()
                    .memory_limit(wmem)
                    .wait()
                    .unwrap()
                    .unwrap();
                #[cfg(target_os = "macos")]
                let status = child.controlled().wait().unwrap().unwrap();
                let res = match status.code() {
                    Some(10) => false,
                    Some(20) => true,
                    e => {
                        let mut ps = state.0.lock().unwrap();
                        if let PortfolioState::Checking(np) = ps.deref_mut() {
                            info!("{config} unexpectedly exited, exit code: {e:?}");
                            let mut stderr = String::new();
                            child.stderr.unwrap().read_to_string(&mut stderr).unwrap();
                            info!("{stderr}");
                            *np -= 1;
                            if *np == 0 {
                                state.1.notify_one();
                            }
                        }
                        return;
                    }
                };
                let mut lock = state.0.lock().unwrap();
                if lock.is_checking() {
                    *lock = PortfolioState::Finished(res, config, certificate);
                    state.1.notify_one();
                }
            });
        }
        let mut result = self.state.1.wait(lock).unwrap();
        if let PortfolioState::Checking(np) = result.deref() {
            assert!(*np == 0);
            error!("all workers unexpectedly exited :(");
            return None;
        }
        let (res, config, certificate) = result.result();
        drop(result);
        self.certificate = certificate;
        info!("best configuration: {config}");
        let pids: Vec<String> = self.engine_pids.iter().map(|p| format!("{}", *p)).collect();
        let pid = pids.join(",");
        let _ = Command::new("pkill")
            .args(["-9", "--parent", &pid])
            .output();
        let mut kill = Command::new("kill");
        kill.arg("-9");
        for p in pids {
            kill.arg(p);
        }
        let _ = kill.output().unwrap();
        self.engine_pids.clear();
        Some(res)
    }

    pub fn check(&mut self) -> Option<bool> {
        let ric3 = self as *mut Self as usize;
        ctrlc::set_handler(move || {
            let ric3 = unsafe { &mut *(ric3 as *mut Portfolio) };
            ric3.terminate();
            exit(124);
        })
        .unwrap();
        self.check_inner()
    }
}

impl Drop for Portfolio {
    fn drop(&mut self) {
        let _ = Command::new("rm")
            .arg("-rf")
            .arg(self.temp_dir.path())
            .output();
    }
}

fn certificate(engine: &mut Portfolio, cfg: &Config, res: bool) {
    if res {
        if cfg.certificate.is_none() && !cfg.certify {
            return;
        }
        if let Some(certificate_path) = &cfg.certificate {
            std::fs::copy(engine.certificate.as_ref().unwrap(), certificate_path).unwrap();
        }
    } else {
        if cfg.certificate.is_none() && !cfg.certify && !cfg.witness {
            return;
        }
        let mut witness = String::new();
        File::open(
            engine
                .certificate
                .as_ref()
                .unwrap()
                .path()
                .as_os_str()
                .to_str()
                .unwrap(),
        )
        .unwrap()
        .read_to_string(&mut witness)
        .unwrap();
        if cfg.witness {
            println!("{witness}");
        }
        if let Some(certificate_path) = &cfg.certificate {
            let mut file: File = File::create(certificate_path).unwrap();
            file.write_all(witness.as_bytes()).unwrap();
        }
    }
    if cfg.certify {
        certifaiger_check(&cfg.model, engine.certificate.as_ref().unwrap().path());
    }
}

pub fn portfolio_main(cfg: Config) {
    let mut engine = Portfolio::new(cfg.clone());
    let res = engine.check();
    match res {
        Some(true) => {
            println!("UNSAT");
            if cfg.witness {
                println!("0");
            }
            certificate(&mut engine, &cfg, true)
        }
        Some(false) => {
            println!("SAT");
            certificate(&mut engine, &cfg, false)
        }
        _ => {
            println!("UNKNOWN");
            if cfg.witness {
                println!("2");
            }
        }
    }
    if let Some(res) = res {
        exit(if res { 20 } else { 10 })
    } else {
        exit(30)
    }
}
