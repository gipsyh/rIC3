#![allow(non_snake_case)]
#![feature(assert_matches, get_mut_unchecked, format_args_nl)]

pub mod bmc;
pub mod deep;
pub mod frontend;
mod gipsat;
pub mod ic3;
pub mod kind;
pub mod options;
pub mod portfolio;
pub mod transys;
pub mod wl;

use aig::{Aig, TernarySimulate};
use logic_form::{ternary::TernaryValue, Cube, Var};
use options::Options;
use std::{
    collections::HashMap,
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

pub fn witness_encode(aig: &Aig, witness: &[Cube]) -> String {
    let mut wit = vec!["1".to_string(), "b".to_string()];
    let map: HashMap<Var, bool> =
        HashMap::from_iter(witness[0].iter().map(|l| (l.var(), l.polarity())));
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
        state.push(TernaryValue::from(r));
        line.push(if r { '1' } else { '0' })
    }
    wit.push(line);
    let mut simulate = TernarySimulate::new(aig, state);
    for c in witness[1..].iter() {
        let map: HashMap<Var, bool> = HashMap::from_iter(c.iter().map(|l| (l.var(), l.polarity())));
        let mut line = String::new();
        let mut input = Vec::new();
        for l in aig.inputs.iter() {
            let r = if let Some(r) = map.get(&Var::new(*l)) {
                *r
            } else {
                true
            };
            line.push(if r { '1' } else { '0' });
            input.push(TernaryValue::from(r));
        }
        wit.push(line);
        simulate.simulate(input);
    }
    let p = aig
        .bads
        .iter()
        .position(|b| simulate.value(*b) == TernaryValue::True)
        .unwrap();
    wit[1] = format!("b{p}");
    wit.push(".\n".to_string());
    wit.join("\n")
}

pub fn check_certifaiger(engine: &mut Box<dyn Engine>, aig: &Aig, option: &Options) {
    if option.witness {
        println!("0");
    }
    if option.certifaiger_path.is_none() && !option.certify {
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
    verify_certifaiger(&certifaiger, option);
}

pub fn verify_certifaiger(certifaiger: &Aig, option: &Options) {
    if let Some(witness) = &option.certifaiger_path {
        certifaiger.to_file(witness, true);
    }
    if !option.certify {
        return;
    }
    let certifaiger_file = tempfile::NamedTempFile::new().unwrap();
    let certifaiger_path = certifaiger_file.path().as_os_str().to_str().unwrap();
    certifaiger.to_file(certifaiger_path, true);
    let output = Command::new("/root/certifaiger/build/check")
        .arg(&option.model)
        .arg(certifaiger_path)
        .output()
        .expect("certifaiger not found");
    if option.verbose > 1 {
        io::stdout().write_all(&output.stdout).unwrap();
    }
    if output.status.success() {
        println!("certifaiger check passed");
    } else {
        panic!("certifaiger check failed");
    }
}

pub fn check_witness(engine: &mut Box<dyn Engine>, aig: &Aig, option: &Options) {
    if option.certifaiger_path.is_none() && !option.certify && !option.witness {
        return;
    }
    let witness = engine.witness(aig);
    if let Some(witness_file) = &option.certifaiger_path {
        let mut file: File = File::create(witness_file).unwrap();
        file.write_all(witness.as_bytes()).unwrap();
    }
    if option.witness {
        println!("{}", witness);
    }
    if !option.certify {
        return;
    }
    let mut wit_file = tempfile::NamedTempFile::new().unwrap();
    wit_file.write_all(witness.as_bytes()).unwrap();
    let wit_path = wit_file.path().as_os_str().to_str().unwrap();
    let output = Command::new("/root/certifaiger/build/simulate")
        .arg(&option.model)
        .arg(wit_path)
        .output()
        .expect("certifaiger not found");
    if option.verbose > 1 {
        io::stdout().write_all(&output.stdout).unwrap();
    }
    if output.status.success() {
        println!("certifaiger check passed");
    } else {
        panic!("certifaiger check failed");
    }
}
