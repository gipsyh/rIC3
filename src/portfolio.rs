use crate::{Options, frontend::aig::certificate::certifaiger_check};
use process_control::{ChildExt, Control};
use std::{
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
    option: Options,
    engines: Vec<Command>,
    temp_dir: TempDir,
    engine_pids: Vec<i32>,
    certificate: Option<NamedTempFile>,
    state: Arc<(Mutex<PortfolioState>, Condvar)>,
}

impl Portfolio {
    pub fn new(option: Options) -> Self {
        let temp_dir = tempfile::TempDir::new_in("/tmp/rIC3/").unwrap();
        let temp_dir_path = temp_dir.path();
        let mut engines = Vec::new();
        let mut new_engine = |args: &str| {
            let args = args.split(" ");
            let mut engine = Command::new(current_exe().unwrap());
            engine.env("RIC3_TMP_DIR", temp_dir_path);
            engine.arg(&option.model);
            engine.arg("-v");
            engine.arg("0");
            for a in args {
                engine.arg(a);
            }
            if option.preprocess.sec {
                engine.arg("--sec");
            }
            if option.preprocess.no_abc {
                engine.arg("--no-abc");
            }
            engines.push(engine);
        };
        new_engine("-e ic3");
        new_engine("-e ic3 --ic3-ctp --rseed 5555");
        new_engine("-e ic3 --ic3-dynamic --rseed 55");
        new_engine("-e ic3 --ic3-ctg");
        new_engine("-e ic3 --ic3-ctg --ic3-ctg-limit 5");
        new_engine("-e ic3 --ic3-ctg --ic3-ctg-max 5 --ic3-ctg-limit 15");
        new_engine("-e ic3 --ic3-ctg --ic3-abs-cst --rseed 55");
        new_engine("-e ic3 --ic3-ctg --ic3-ctp");
        new_engine("-e ic3 --ic3-inn");
        new_engine("-e ic3 --ic3-ctg --ic3-inn");
        new_engine("-e ic3 --ic3-ctg --ic3-ctg-limit 5 --ic3-inn");
        new_engine("-e bmc --step 1");
        new_engine("-e bmc --step 10");
        new_engine("-e bmc --bmc-kissat --step 70");
        new_engine("-e bmc --bmc-kissat --step 135");
        new_engine("-e kind --step 1 --kind-simple-path");
        let ps = PortfolioState::new(engines.len());
        Self {
            option,
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
        let lock = self.state.0.lock().unwrap();
        for mut engine in take(&mut self.engines) {
            let certificate = if self.option.certificate.is_some()
                || self.option.certify
                || self.option.witness
            {
                let certificate = tempfile::NamedTempFile::new_in(self.temp_dir.path()).unwrap();
                let certify_path = certificate.path().as_os_str().to_str().unwrap();
                engine.arg(certify_path);
                Some(certificate)
            } else {
                None
            };
            let mut child = engine.stderr(Stdio::piped()).spawn().unwrap();
            self.engine_pids.push(child.id() as i32);
            let option = self.option.clone();
            let state = self.state.clone();
            spawn(move || {
                let mut config = engine
                    .get_args()
                    .skip(4)
                    .map(|cstr| cstr.to_str().unwrap())
                    .collect::<Vec<&str>>();
                config.pop();
                let config = config.join(" ");
                if option.verbose > 1 {
                    println!("start engine: {config}");
                }
                #[cfg(target_os = "linux")]
                let status = child
                    .controlled()
                    .memory_limit(1024 * 1024 * 1024 * 16)
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
                            if option.verbose > 0 {
                                println!("{config} unexpectedly exited, exit code: {:?}", e);
                                let mut stderr = String::new();
                                child.stderr.unwrap().read_to_string(&mut stderr).unwrap();
                                print!("stderr:");
                                print!("{}", stderr);
                            }
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
            if self.option.verbose > 0 {
                println!("all workers unexpectedly exited :(");
            }
            return None;
        }
        let (res, config, certificate) = result.result();
        drop(result);
        self.certificate = certificate;
        println!("best configuration: {}", config);
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

fn certificate(engine: &mut Portfolio, option: &Options, res: bool) {
    if res {
        if option.certificate.is_none() && !option.certify {
            return;
        }
        if let Some(certificate_path) = &option.certificate {
            std::fs::copy(engine.certificate.as_ref().unwrap(), certificate_path).unwrap();
        }
    } else {
        if option.certificate.is_none() && !option.certify && !option.witness {
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
        if option.witness {
            println!("{}", witness);
        }
        if let Some(certificate_path) = &option.certificate {
            let mut file: File = File::create(certificate_path).unwrap();
            file.write_all(witness.as_bytes()).unwrap();
        }
    }
    if !option.certify {
        return;
    }
    certifaiger_check(
        option,
        engine
            .certificate
            .as_ref()
            .unwrap()
            .path()
            .as_os_str()
            .to_str()
            .unwrap(),
    );
}

pub fn portfolio_main(options: Options) {
    let mut engine = Portfolio::new(options.clone());
    let res = engine.check();
    if options.verbose > 0 {
        print!("result: ");
    }
    match res {
        Some(true) => {
            if options.verbose > 0 {
                println!("safe");
            }
            if options.witness {
                println!("0");
            }
            certificate(&mut engine, &options, true)
        }
        Some(false) => {
            if options.verbose > 0 {
                println!("unsafe");
            }
            certificate(&mut engine, &options, false)
        }
        _ => {
            if options.verbose > 0 {
                println!("unknown");
            }
            if options.witness {
                println!("2");
            }
        }
    }
    if let Some(res) = res {
        exit(if res { 20 } else { 10 })
    } else {
        exit(0)
    }
}
