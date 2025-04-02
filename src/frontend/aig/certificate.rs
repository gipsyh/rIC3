use aig::{Aig, TernarySimulate};
use giputils::hash::GHashMap;
use logic_form::{Lbool, Var};

use super::AigFrontend;
use crate::{Engine, Proof, Witness, options::Options};
use std::{
    fs::File,
    io::{self, Write},
    process::Command,
};

impl AigFrontend {
    pub fn certificate(&self, engine: &mut Box<dyn Engine>, res: bool) {
        if res {
            if self.opt.certificate.is_none() && !self.opt.certify {
                return;
            }
            let proof = engine.proof(&self.origin_ts);
            let certifaiger = self.proof(proof);
            if let Some(certificate_path) = &self.opt.certificate {
                certifaiger.to_file(certificate_path.to_str().unwrap(), true);
            }
            if !self.opt.certify {
                return;
            }
            let certificate_file = tempfile::NamedTempFile::new().unwrap();
            let certificate_path = certificate_file.path().as_os_str().to_str().unwrap();
            certifaiger.to_file(certificate_path, true);
            certifaiger_check(&self.opt, certificate_path);
        } else {
            if self.opt.certificate.is_none() && !self.opt.certify && !self.opt.witness {
                return;
            }
            let witness = engine.witness(&self.origin_ts);
            let witness = self.witness(witness);
            if self.opt.witness {
                println!("{}", witness);
            }
            if let Some(certificate_path) = &self.opt.certificate {
                let mut file: File = File::create(certificate_path).unwrap();
                file.write_all(witness.as_bytes()).unwrap();
            }
            if !self.opt.certify {
                return;
            }
            let mut wit_file = tempfile::NamedTempFile::new().unwrap();
            wit_file.write_all(witness.as_bytes()).unwrap();
            let wit_path = wit_file.path().as_os_str().to_str().unwrap();
            certifaiger_check(&self.opt, wit_path);
        }
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
            certifaiger.to_file(certificate_path, true);
        }
        if !option.certify {
            return;
        }
        let certificate_file = tempfile::NamedTempFile::new().unwrap();
        certifaiger.to_file(certificate_file.path(), true);
        certifaiger_check(option, certificate_file.path());
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

    pub fn witness(&self, wit: Witness) -> String {
        let mut res = vec!["1".to_string(), "b".to_string()];
        let map: GHashMap<Var, bool> =
            GHashMap::from_iter(wit.init.iter().map(|l| (l.var(), l.polarity())));
        let mut line = String::new();
        let mut state = Vec::new();
        for l in self.origin_aig.latchs.iter() {
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
        res.push(line);
        let mut simulate = TernarySimulate::new(&self.origin_aig, state);
        for c in wit.wit.iter() {
            let map: GHashMap<Var, bool> =
                GHashMap::from_iter(c.iter().map(|l| (l.var(), l.polarity())));
            let mut line = String::new();
            let mut input = Vec::new();
            for l in self.origin_aig.inputs.iter() {
                let r = if let Some(r) = map.get(&Var::new(*l)) {
                    *r
                } else {
                    true
                };
                line.push(if r { '1' } else { '0' });
                input.push(Lbool::from(r));
            }
            res.push(line);
            simulate.simulate(input);
        }
        let p = self
            .origin_aig
            .bads
            .iter()
            .position(|b| simulate.value(*b).is_true())
            .unwrap();
        res[1] = format!("b{p}");
        res.push(".\n".to_string());
        res.join("\n")
    }

    pub fn proof(&self, proof: Proof) -> Aig {
        let mut certifaiger = Aig::from(&proof.proof);
        certifaiger = certifaiger.reencode();
        certifaiger.symbols.clear();
        for i in 0..self.origin_aig.inputs.len() {
            certifaiger.set_symbol(
                certifaiger.inputs[i],
                &format!("= {}", self.origin_aig.inputs[i] * 2),
            );
        }
        for i in 0..self.origin_aig.latchs.len() {
            certifaiger.set_symbol(
                certifaiger.latchs[i].input,
                &format!("= {}", self.origin_aig.latchs[i].input * 2),
            );
        }
        certifaiger
    }
}

pub fn certifaiger_check<P: AsRef<Path>>(option: &Options, certificate: P) {
    let certificate = certificate.as_ref();
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
            &format!("{}:{}", certificate.display(), certificate.display()),
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
            _ => panic!(
                "certifaiger maybe not avaliable, please build docker image from https://github.com/Froleyks/certifaiger"
            ),
        }
    }
}
