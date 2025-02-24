#![allow(non_snake_case)]
#![feature(get_mut_unchecked)]

pub mod bmc;
pub mod frontend;
mod gipsat;
pub mod ic3;
pub mod kind;
pub mod options;
pub mod portfolio;
pub mod transys;

use aig::{Aig, TernarySimulate};
use giputils::hash::GHashMap;
use logic_form::{Lbool, LitVec, Var};
use options::Options;
use std::{
    fs::File,
    io::{self, Write},
    process::Command,
};

pub trait Engine {
    fn check(&mut self) -> Option<bool>;

    fn certifaiger(&mut self, _aig: &Aig) -> Aig {
        panic!("unsupport certifaiger");
    }

    fn witness(&mut self, _aig: &Aig) -> String {
        panic!("unsupport witness");
    }

    fn statistic(&mut self) {}
}

pub fn witness_encode(aig: &Aig, witness: &[LitVec]) -> String {
    let mut wit = vec!["1".to_string(), "b".to_string()];
    let map: GHashMap<Var, bool> =
        GHashMap::from_iter(witness[0].iter().map(|l| (l.var(), l.polarity())));
    let mut line = String::new();
    let mut state = Vec::new();
    for l in aig.latchs.iter() {
        let r = if let Some(r) = l.init {
            r
        } else if let Some(r) = map.get(&Var::new(l.input)) {
            *r
        } else {
            true
        };
        state.push(Lbool::from(r));
        line.push(if r { '1' } else { '0' })
    }
    wit.push(line);
    let mut simulate = TernarySimulate::new(aig, state);
    for c in witness[1..].iter() {
        let map: GHashMap<Var, bool> =
            GHashMap::from_iter(c.iter().map(|l| (l.var(), l.polarity())));
        let mut line = String::new();
        let mut input = Vec::new();
        for l in aig.inputs.iter() {
            let r = if let Some(r) = map.get(&Var::new(*l)) {
                *r
            } else {
                true
            };
            line.push(if r { '1' } else { '0' });
            input.push(Lbool::from(r));
        }
        wit.push(line);
        simulate.simulate(input);
    }
    let p = aig
        .bads
        .iter()
        .position(|b| simulate.value(*b).is_true())
        .unwrap();
    wit[1] = format!("b{p}");
    wit.push(".\n".to_string());
    wit.join("\n")
}

pub fn certificate(engine: &mut Box<dyn Engine>, aig: &Aig, option: &Options, res: bool) {
    if res {
        if option.certificate.is_none() && !option.certify {
            return;
        }
        let mut certifaiger = engine.certifaiger(aig);
        certifaiger = certifaiger.reencode();
        certifaiger.symbols.clear();
        for i in 0..aig.inputs.len() {
            certifaiger.set_symbol(certifaiger.inputs[i], &format!("= {}", aig.inputs[i] * 2));
        }
        for i in 0..aig.latchs.len() {
            certifaiger.set_symbol(
                certifaiger.latchs[i].input,
                &format!("= {}", aig.latchs[i].input * 2),
            );
        }
        if let Some(certificate_path) = &option.certificate {
            certifaiger.to_file(certificate_path.to_str().unwrap(), true);
        }
        if !option.certify {
            return;
        }
        let certificate_file = tempfile::NamedTempFile::new().unwrap();
        let certificate_path = certificate_file.path().as_os_str().to_str().unwrap();
        certifaiger.to_file(certificate_path, true);
        certifaiger_check(option, certificate_path);
    } else {
        if option.certificate.is_none() && !option.certify && !option.witness {
            return;
        }
        let witness = engine.witness(aig);
        if option.witness {
            println!("{}", witness);
        }
        if let Some(certificate_path) = &option.certificate {
            let mut file: File = File::create(certificate_path).unwrap();
            file.write_all(witness.as_bytes()).unwrap();
        }
        if !option.certify {
            return;
        }
        let mut wit_file = tempfile::NamedTempFile::new().unwrap();
        wit_file.write_all(witness.as_bytes()).unwrap();
        let wit_path = wit_file.path().as_os_str().to_str().unwrap();
        certifaiger_check(option, wit_path);
    }
}

fn certifaiger_check(option: &Options, certificate: &str) {
    let output = Command::new("docker")
        .args([
            "run",
            "--rm",
            "-v",
            &format!(
                "{}:{}",
                option.model.as_path().display(),
                option.model.as_path().display()
            ),
            "-v",
            &format!("{}:{}", certificate, certificate),
            "certifaiger",
        ])
        .arg(&option.model)
        .arg(certificate)
        .output()
        .unwrap();
    if output.status.success() {
        println!("certifaiger check passed");
    } else {
        if option.verbose > 1 {
            io::stdout().write_all(&output.stdout).unwrap();
            io::stderr().write_all(&output.stderr).unwrap();
        }
        match output.status.code() {
            Some(1) => panic!("certifaiger check failed"),
            _ => panic!("certifaiger maybe not avaliable, please build docker image from https://github.com/Froleyks/certifaiger"),
           }
    }
}
