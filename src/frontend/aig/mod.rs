use super::Frontend;
use crate::{
    Proof, Witness,
    config::Config,
    transys::{Transys, TransysIf},
};
use aig::{Aig, AigEdge};
use giputils::hash::GHashMap;
use log::{debug, error, warn};
use logicrs::{Lbool, Lit, LitVec, Var, VarSymbols, VarVMap};
use std::{
    fmt::Display,
    path::Path,
    process::{Command, exit},
};

impl From<&Transys> for Aig {
    fn from(ts: &Transys) -> Self {
        let mut aig = Aig::new();
        let mut map = GHashMap::new();
        map.insert(Var::CONST, AigEdge::from_lit(Var::CONST.lit()));
        for i in ts.input.iter() {
            let t = aig.new_input();
            map.insert(*i, AigEdge::new(t, false));
        }
        for &f in ts.latch.iter() {
            let t = aig.new_leaf_node();
            map.insert(f, AigEdge::new(t, false));
        }
        for (v, rel) in ts.rel.iter() {
            if ts.rel.has_rel(v) && !v.is_constant() {
                assert!(!map.contains_key(&v));
                let mut r = Vec::new();
                for rel in rel {
                    let last = rel.last();
                    assert!(last.var() == v);
                    if last.polarity() {
                        let mut rel = !rel;
                        rel.pop();
                        r.push(aig.trivial_new_ands_node(
                            rel.iter().map(|l| map[&l.var()].not_if(!l.polarity())),
                        ));
                    }
                }
                let n = aig.trivial_new_ors_node(r);
                map.insert(v, n);
            }
        }
        let map_lit = |l: Lit| map[&l.var()].not_if(!l.polarity());
        for l in ts.latch.iter() {
            let next = map_lit(ts.next[l]);
            let init = ts.init.get(l).map(|&l| map_lit(l));
            aig.add_latch(map[l].node_id(), next, init);
        }
        for &b in ts.bad.iter() {
            aig.bads.push(map_lit(b));
        }
        for c in ts.constraint() {
            aig.constraints.push(map_lit(c));
        }
        if !ts.justice.is_empty() {
            aig.justice = vec![ts.justice.iter().map(|&j| map_lit(j)).collect()];
        }
        aig
    }
}

impl Transys {
    pub fn from_aig(aig: &Aig, compact: bool) -> Transys {
        let input: Vec<Var> = aig.inputs.iter().map(|x| Var::new(*x)).collect();
        let mut latch = Vec::new();
        let mut next = GHashMap::new();
        let mut init = GHashMap::new();
        for l in aig.latchs.iter() {
            let lv = Var::from(l.input);
            latch.push(lv);
            next.insert(lv, l.next.to_lit());
            if let Some(i) = l.init {
                init.insert(lv, i.to_lit());
            }
        }
        let bad = aig.bads.iter().map(|c| c.to_lit()).collect();
        let constraint: LitVec = aig.constraints.iter().map(|c| c.to_lit()).collect();
        let mut justice: LitVec = aig
            .justice
            .first()
            .map(|j| j.iter().map(|e| e.to_lit()).collect())
            .unwrap_or_default();
        justice.extend(aig.fairness.iter().map(|f| f.to_lit()));
        let rel = aig.cnf(compact);
        Transys {
            input,
            latch,
            next,
            init,
            bad,
            constraint,
            justice,
            rel,
        }
    }
}

fn aig_preprocess(aig: &Aig) -> (Aig, VarVMap) {
    let (mut aig, restore) = aig.coi_refine();
    aig.constraints.retain(|e| !e.is_constant(true));
    (aig, restore)
}

fn aig_symbols(aig: &Aig) -> VarSymbols {
    let mut symbol = VarSymbols::new();
    for &x in aig.inputs.iter().chain(aig.latchs.iter().map(|l| &l.input)) {
        if let Some(s) = aig.symbols.get(&x) {
            for s in s.split(' ') {
                let mut rs = s;
                let mut idx = 0;
                if s.ends_with(']')
                    && let Some(start) = s.rfind('[')
                {
                    idx = s[start + 1..s.len() - 1].parse::<usize>().unwrap();
                    rs = &s[..start];
                }
                symbol.insert(Var::from(x), rs.to_string(), idx);
            }
        }
    }
    symbol
}

pub struct AigFrontend {
    oaig: Aig,
    ots: Transys,
    ts: Transys,
    ts_symbols: VarSymbols,
    rst: VarVMap,
}

impl AigFrontend {
    pub fn new(cfg: &Config) -> Self {
        let mut oaig = Aig::from_file(&cfg.model);
        if !oaig.outputs.is_empty() {
            if oaig.bads.is_empty() {
                oaig.bads = std::mem::take(&mut oaig.outputs);
                warn!(
                    "property not found, moved {} outputs to bad properties",
                    oaig.bads.len()
                );
            } else {
                warn!("outputs in aiger are ignored");
                oaig.outputs.clear();
            }
        }
        let mut aig = oaig.clone();
        if !aig.justice.is_empty() {
            if !aig.bads.is_empty() {
                error!(
                    "rIC3 does not support solving both safety and liveness properties simultaneously"
                );
                panic!();
            }
        } else {
            if !aig.fairness.is_empty() {
                warn!("fairness constraints are ignored when solving the safety property");
                aig.fairness.clear();
            }
            if aig.bads.is_empty() {
                warn!("no property to be checked");
                if let Some(certificate) = &cfg.unsat_certificate {
                    let mut map = aig.inputs.clone();
                    map.extend(aig.latchs.iter().map(|l| l.input));
                    for x in map {
                        aig.set_symbol(x, &format!("= {}", x * 2));
                    }
                    aig.to_file(certificate, true);
                }
                println!("UNSAT");
                exit(20);
            }
        }
        let ots = Transys::from_aig(&aig, true);
        let osymbols = aig_symbols(&aig);
        let (aig, rst) = aig_preprocess(&aig);
        let inv_rst = rst.inverse();
        let ts_symbols = osymbols.map_var(inv_rst.try_map_fn());
        let ts = Transys::from_aig(&aig, true);
        Self {
            oaig,
            ots,
            ts,
            ts_symbols,
            rst,
        }
    }

    pub fn is_safety(&self) -> bool {
        if !self.oaig.bads.is_empty() {
            true
        } else {
            assert!(!self.ts.justice.is_empty());
            false
        }
    }
}

impl Frontend for AigFrontend {
    fn ts(&mut self) -> (Transys, VarSymbols) {
        (self.ts.clone(), self.ts_symbols.clone())
    }

    fn safe_certificate(&mut self, proof: Proof) -> Box<dyn Display> {
        if !self.is_safety() {
            error!("rIC3 does not support certificate generation for safe liveness properties");
            panic!();
        }
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
        Box::new(certifaiger)
    }

    fn unsafe_certificate(&mut self, witness: Witness) -> Box<dyn Display> {
        let mut wit = witness.filter_map_var(|v: Var| self.rst.get(&v).copied());
        let mut res = vec!["1".to_string()];
        if self.is_safety() {
            res.push(format!("b{}", witness.bad_id));
        } else {
            res.push("j0".to_string());
        }
        wit.exact_init_state(&self.ots);
        let mut line = String::new();
        let mut lbstate = Vec::new();
        for l in wit.state[0].iter() {
            lbstate.push(Lbool::from(l.polarity()));
            line.push(if l.polarity() { '1' } else { '0' })
        }
        res.push(line);
        let mut line = String::new();
        for i in wit.input[0].iter() {
            line.push(if i.polarity() { '1' } else { '0' })
        }
        res.push(line);
        for c in wit.input[1..].iter() {
            let map: GHashMap<Var, bool> =
                GHashMap::from_iter(c.iter().map(|l| (l.var(), l.polarity())));
            let mut line = String::new();
            let mut input = Vec::new();
            for l in self.oaig.inputs.iter() {
                let r = if let Some(r) = map.get(&Var::new(*l)) {
                    *r
                } else {
                    true
                };
                line.push(if r { '1' } else { '0' });
                input.push(Lbool::from(r));
            }
            res.push(line);
        }
        res.push(".\n".to_string());
        Box::new(res.join("\n"))
    }

    fn certify(&mut self, model: &Path, cert: &Path) -> bool {
        certifaiger_check(model, cert)
    }
}

pub fn certifaiger_check<M: AsRef<Path>, C: AsRef<Path>>(model: M, certificate: C) -> bool {
    let certificate = certificate.as_ref();
    let output = Command::new("docker")
        .args([
            "run",
            "--rm",
            "--pull=never",
            "-v",
            &format!("{}:{}", model.as_ref().display(), model.as_ref().display()),
            "-v",
            &format!("{}:{}", certificate.display(), certificate.display()),
            "ghcr.io/gipsyh/certifaiger",
        ])
        .arg(model.as_ref())
        .arg(certificate)
        .output()
        .unwrap();
    if output.status.success() {
        true
    } else {
        debug!("{}", String::from_utf8_lossy(&output.stdout));
        debug!("{}", String::from_utf8_lossy(&output.stderr));
        match output.status.code() {
            Some(1) => (),
            _ => error!(
                "certifaiger maybe not avaliable, please `docker pull ghcr.io/gipsyh/certifaiger:latest`"
            ),
        }
        false
    }
}
