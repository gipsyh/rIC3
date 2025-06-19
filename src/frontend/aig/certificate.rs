use aig::{Aig, TernarySimulate};
use giputils::hash::GHashMap;
use log::{debug, info};
use logicrs::{Lbool, Var};

use super::AigFrontend;
use crate::{Proof, Witness, config::Config, transys::TransysIf};
use std::{path::Path, process::Command};

impl AigFrontend {
    pub fn witness(&self, wit: Witness) -> String {
        let mut res = vec!["1".to_string(), "b".to_string()];
        let map: GHashMap<Var, bool> =
            GHashMap::from_iter(wit.state[0].iter().map(|l| (l.var(), l.polarity())));
        let mut line = String::new();
        let mut state = Vec::new();
        for l in self.origin_aig.latchs.iter() {
            let r = if let Some(r) = map.get(&Var::new(l.input)) {
                *r
            } else if let Some(r) = l.init
                && let Some(r) = r.try_to_constant()
            {
                r
            } else {
                true
            };
            state.push(Lbool::from(r));
            line.push(if r { '1' } else { '0' })
        }
        res.push(line);
        let mut simulate = TernarySimulate::new(&self.origin_aig, state);
        for c in wit.input.iter() {
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
        if self.is_safety() {
            let p = self
                .origin_aig
                .bads
                .iter()
                .position(|b| simulate.value(*b).is_true())
                .unwrap();
            res[1] = format!("b{p}");
        } else {
            res[1] = "j0".to_string();
        }
        res.push(".\n".to_string());
        res.join("\n")
    }

    pub fn proof(&self, proof: Proof) -> Aig {
        let mut certifaiger = Aig::from(&proof.proof);
        certifaiger = certifaiger.reencode();
        certifaiger.symbols.clear();
        for (i, v) in proof.proof.input().enumerate() {
            if let Some(r) = self.rst.get(&v) {
                certifaiger.set_symbol(certifaiger.inputs[i], &format!("= {}", (**r) * 2));
            }
        }
        for (i, v) in proof.proof.latch().enumerate() {
            if let Some(r) = self.rst.get(&v) {
                certifaiger.set_symbol(certifaiger.latchs[i].input, &format!("= {}", (**r) * 2));
            }
        }
        certifaiger
    }
}

pub fn certifaiger_check<P: AsRef<Path>>(cfg: &Config, certificate: P) {
    let certificate = certificate.as_ref();
    let output = Command::new("docker")
        .args([
            "run",
            "--rm",
            "--pull=never",
            "-v",
            &format!(
                "{}:{}",
                cfg.model.as_path().display(),
                cfg.model.as_path().display()
            ),
            "-v",
            &format!("{}:{}", certificate.display(), certificate.display()),
            "ghcr.io/gipsyh/certifaiger",
        ])
        .arg(&cfg.model)
        .arg(certificate)
        .output()
        .unwrap();
    if output.status.success() {
        info!("certifaiger check passed");
    } else {
        debug!("{}", String::from_utf8_lossy(&output.stdout));
        debug!("{}", String::from_utf8_lossy(&output.stderr));
        match output.status.code() {
            Some(1) => panic!("certifaiger check failed"),
            _ => panic!(
                "certifaiger maybe not avaliable, please `docker pull ghcr.io/gipsyh/certifaiger:latest`"
            ),
        }
    }
}
