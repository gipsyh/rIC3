use crate::Options;
use process_control::{ChildExt, Control};
use std::{
    env::current_exe,
    mem::take,
    process::{Command, Stdio},
    sync::mpsc::channel,
    thread::spawn,
};

pub struct Portfolio {
    option: Options,
    engines: Vec<Command>,
}

impl Portfolio {
    pub fn new(option: Options) -> Self {
        let mut engines = Vec::new();
        let mut new_engine = |args: &[&str]| {
            let mut engine = Command::new(current_exe().unwrap());
            engine.args(["-v", "0"]);
            engine.arg(&option.model);
            engine.args(args);
            engines.push(engine);
        };
        // ic3
        new_engine(&["--ic3"]);
        // ic3
        new_engine(&["--ic3", "--ic3-ctp"]);
        // ic3 with ctg
        new_engine(&["--ic3", "--ic3-ctg"]);
        // ic3 with xor
        new_engine(&["--ic3", "--ic3-ctg", "--ic3-ctp", "--ic3-xor"]);
        // bmc
        new_engine(&["--bmc", "--step", "10"]);
        // bmc kissat step 70
        new_engine(&["--bmc", "--bmc-kissat", "--step", "70"]);
        // bmc kissat step 130
        new_engine(&["--bmc", "--bmc-kissat", "--step", "135"]);
        // kind
        new_engine(&["--kind", "--step", "10", "--kind-no-bmc"]);
        Self { option, engines }
    }

    pub fn check(&mut self) -> bool {
        let (tx, rx) = channel::<(String, bool)>();
        let mut engines = Vec::new();
        for mut engine in take(&mut self.engines) {
            let mut child = engine.stderr(Stdio::piped()).spawn().unwrap();
            engines.push(child.id() as i32);
            let tx = tx.clone();
            let option = self.option.clone();
            spawn(move || {
                let config = engine
                    .get_args()
                    .skip(2)
                    .map(|cstr| cstr.to_str().unwrap())
                    .collect::<Vec<&str>>()
                    .join(" ");
                if option.verbose > 1 {
                    println!("start engine: {config}");
                }
                let output = child
                    .controlled()
                    .memory_limit(1024 * 1024 * 1024 * 16)
                    .wait()
                    .unwrap();
                if let Some(status) = output {
                    let res = match status.code() {
                        Some(10) => false,
                        Some(20) => true,
                        e => {
                            if option.verbose > 0 {
                                println!("{config} unsuccessfully exited, exit code: {:?}", e);
                            }
                            return;
                        }
                    };
                    let _ = tx.send((config, res));
                } else {
                    let _ = child.kill();
                };
            });
        }
        let (config, res) = rx.recv().unwrap();
        println!("best configuration: {config}");
        for pid in engines {
            let _ = nix::sys::signal::kill(
                nix::unistd::Pid::from_raw(pid),
                nix::sys::signal::Signal::SIGKILL,
            );
        }
        res
    }
}
