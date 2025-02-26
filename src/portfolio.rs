use crate::{Engine, Options};
use aig::Aig;
use process_control::{ChildExt, Control};
use std::{
    env::current_exe,
    fs::File,
    io::Read,
    mem::take,
    process::{exit, Command, Stdio},
    sync::{Arc, Condvar, Mutex},
    thread::spawn,
};
use tempfile::{NamedTempFile, TempDir};

#[derive(Default)]
enum PortfolioState {
    #[default]
    Checking,
    Finished(bool, String, Option<NamedTempFile>),
    Terminate,
}

impl PortfolioState {
    fn is_checking(&self) -> bool {
        matches!(self, Self::Checking)
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
    _model_file: NamedTempFile,
    engines: Vec<Command>,
    temp_dir: TempDir,
    engine_pids: Vec<i32>,
    certificate: Option<NamedTempFile>,
    result: Arc<(Mutex<PortfolioState>, Condvar)>,
}

impl Portfolio {
    pub fn new(option: Options, aig: &Aig) -> Self {
        let temp_dir = tempfile::TempDir::new_in("/tmp/rIC3/").unwrap();
        let temp_dir_path = temp_dir.path();
        let model_file = tempfile::NamedTempFile::with_suffix_in(".aig", temp_dir_path).unwrap();
        let model_path = model_file.path().as_os_str().to_str().unwrap();
        aig.to_file(model_path, false);
        let mut engines = Vec::new();
        let mut new_engine = |args: &str| {
            let args = args.split(" ");
            let mut engine = Command::new(current_exe().unwrap());
            engine.env("RIC3_TMP_DIR", temp_dir_path);
            engine.arg(model_path);
            engine.arg("-v");
            engine.arg("0");
            for a in args {
                engine.arg(a);
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
        Self {
            option,
            _model_file: model_file,
            engines,
            temp_dir,
            certificate: None,
            engine_pids: Default::default(),
            result: Arc::new((Mutex::new(PortfolioState::default()), Condvar::new())),
        }
    }

    pub fn terminate(&mut self) {
        let Ok(mut lock) = self.result.0.try_lock() else {
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
        let lock = self.result.0.lock().unwrap();
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
            let result = self.result.clone();
            spawn(move || {
                let config = engine
                    .get_args()
                    .skip(4)
                    .map(|cstr| cstr.to_str().unwrap())
                    .collect::<Vec<&str>>()
                    .join(" ");
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
                        if option.verbose > 0 && result.0.lock().unwrap().is_checking() {
                            println!("{config} unsuccessfully exited, exit code: {:?}", e);
                        }
                        return;
                    }
                };
                let mut lock = result.0.lock().unwrap();
                if lock.is_checking() {
                    *lock = PortfolioState::Finished(res, config, certificate);
                    result.1.notify_one();
                }
            });
        }
        let mut result = self.result.1.wait(lock).unwrap();
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
}

impl Drop for Portfolio {
    fn drop(&mut self) {
        let _ = Command::new("rm")
            .arg("-rf")
            .arg(self.temp_dir.path())
            .output();
    }
}

impl Engine for Portfolio {
    fn check(&mut self) -> Option<bool> {
        let ric3 = self as *mut Self as usize;
        ctrlc::set_handler(move || {
            let ric3 = unsafe { &mut *(ric3 as *mut Portfolio) };
            ric3.terminate();
            exit(124);
        })
        .unwrap();
        self.check_inner()
    }

    fn certifaiger(&mut self, _aig: &aig::Aig) -> Aig {
        let certificate = take(&mut self.certificate);
        Aig::from_file(certificate.unwrap().path().as_os_str().to_str().unwrap())
    }

    fn witness(&mut self, _aig: &Aig) -> String {
        let mut res = String::new();
        let certificate = take(&mut self.certificate);
        File::open(certificate.unwrap().path().as_os_str().to_str().unwrap())
            .unwrap()
            .read_to_string(&mut res)
            .unwrap();
        res
    }
}
