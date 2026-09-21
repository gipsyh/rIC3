use super::Frontend;
use crate::{
    McBlCertificate,
    transys::{Transys, TransysIf},
};
use aig::{Aig, AigEdge};
use giputils::{
    gvec::Gvec,
    hash::{GHashMap, GHashSet},
};
use log::{debug, error, warn};
use logicrs::{Lbool, Lit, LitVec, Var, VarSymbols};
use std::{fmt::Display, path::Path, process::Command};

impl From<&Transys> for Aig {
    fn from(ts: &Transys) -> Self {
        let mut aig = Aig::new();
        let mut map = GHashMap::new();
        map.insert(Var::CONST, AigEdge::from(Var::CONST));
        for i in ts.input.iter() {
            let t = aig.new_input();
            map.insert(*i, AigEdge::from(t));
        }
        for &f in ts.latch.iter() {
            let t = aig.new_leaf_node();
            map.insert(f, AigEdge::from(t));
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
            aig.add_latch(Lit::from(map[l]).var(), next, init);
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
        let input: Vec<Var> = aig.inputs.clone();
        let mut latch = Vec::new();
        let mut next = GHashMap::new();
        let mut init = GHashMap::new();
        for l in aig.latchs.iter() {
            let lv = l.input;
            latch.push(lv);
            next.insert(lv, l.next.into());
            if let Some(i) = l.init {
                init.insert(lv, i.into());
            }
        }
        let bad = aig.bads.iter().map(|c| (*c).into()).collect();
        let constraint: LitVec = aig.constraints.iter().map(|c| (*c).into()).collect();
        let mut justice: LitVec = aig
            .justice
            .first()
            .map(|j| j.iter().map(|e| (*e).into()).collect())
            .unwrap_or_default();
        justice.extend(aig.fairness.iter().map(|f| Lit::from(*f)));
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

    fn from_aig_compact(aig: &Aig) -> (Transys, Gvec<Var>) {
        let (rel, map) = aig.cnf_compact();
        let map_var = |v: Var| {
            let mapped = map[*v];
            assert!(v.is_constant() || !mapped.is_constant());
            mapped
        };
        let map_lit = |e: AigEdge| Lit::from(e).map_var(map_var);
        let input = aig.inputs.iter().copied().map(map_var).collect();
        let mut latch = Vec::with_capacity(aig.latchs.len());
        let mut next = GHashMap::new();
        let mut init = GHashMap::new();
        for l in &aig.latchs {
            let v = map_var(l.input);
            latch.push(v);
            next.insert(v, map_lit(l.next));
            if let Some(i) = l.init {
                init.insert(v, map_lit(i));
            }
        }
        let bad = aig.bads.iter().copied().map(map_lit).collect();
        let constraint = aig.constraints.iter().copied().map(map_lit).collect();
        let mut justice: LitVec = aig
            .justice
            .first()
            .map(|j| j.iter().copied().map(map_lit).collect())
            .unwrap_or_default();
        justice.extend(aig.fairness.iter().copied().map(map_lit));
        (
            Transys {
                input,
                latch,
                next,
                init,
                bad,
                constraint,
                justice,
                rel,
            },
            map,
        )
    }
}

pub struct AigFrontend {
    ts: Transys,
    ts_symbols: VarSymbols,
    original_vars: Vec<Var>,
}

impl AigFrontend {
    pub fn new(mut aig: Aig) -> Self {
        if !aig.outputs.is_empty() {
            if aig.bads.is_empty() {
                aig.bads = std::mem::take(&mut aig.outputs);
                warn!(
                    "property not found, moved {} outputs to bad properties",
                    aig.bads.len()
                );
            } else {
                warn!("outputs in aiger are ignored");
                aig.outputs.clear();
            }
        } else if aig.bads.is_empty() {
            warn!("empty property in aiger");
            aig.bads.push(AigEdge::constant(false));
        }
        if !aig.justice.is_empty() {
            if !aig.bads.is_empty() {
                error!(
                    "rIC3 does not support solving both safety and liveness properties simultaneously"
                );
                panic!();
            }
        } else if !aig.fairness.is_empty() {
            warn!("fairness constraints are ignored when solving the safety property");
            aig.fairness.clear();
        }
        aig.comb_simplify();
        let (aig, coi_map) = aig.coi_simplify();
        let (ts, map) = Transys::from_aig_compact(&aig);
        let ts_symbols = VarSymbols::new();
        let mut original_vars = vec![Var::CONST; ts.rel.num_var()];
        for (original, &refined) in coi_map.iter().enumerate() {
            if !refined.is_none() {
                let new = map[*refined];
                if !new.is_constant() {
                    original_vars[usize::from(new)] = Var::new(original);
                }
            }
        }
        Self {
            ts,
            ts_symbols,
            original_vars,
        }
    }

    pub fn is_safety(&self) -> bool {
        if !self.ts.bad.is_empty() {
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

    fn bl_certificate(&mut self, cert: McBlCertificate) -> Box<dyn Display> {
        let leaf: GHashSet<Var> = self.ts.input().chain(self.ts.latch()).collect();
        match cert {
            McBlCertificate::UNSAT(proof) => {
                if !self.is_safety() {
                    error!(
                        "rIC3 does not support certificate generation for safe liveness properties"
                    );
                    panic!();
                }
                let mut certifaiger = Aig::from(&proof.proof);
                certifaiger = certifaiger.reencode();
                certifaiger.symbols.clear();
                for (i, v) in proof.proof.input().enumerate() {
                    if leaf.contains(&v) {
                        let original = self.original_vars[usize::from(v)];
                        certifaiger
                            .set_symbol(certifaiger.inputs[i], &format!("= {}", *original * 2));
                    }
                }
                for (i, v) in proof.proof.latch().enumerate() {
                    if leaf.contains(&v) {
                        let original = self.original_vars[usize::from(v)];
                        certifaiger.set_symbol(
                            certifaiger.latchs[i].input,
                            &format!("= {}", *original * 2),
                        );
                    }
                }
                Box::new(certifaiger)
            }
            McBlCertificate::SAT(bl_cex) => {
                let mut cex = bl_cex.filter(|v| leaf.contains(&v.var()));
                let mut res = vec!["1".to_string()];
                if self.is_safety() {
                    res.push(format!("b{}", bl_cex.bad_id));
                } else {
                    res.push("j0".to_string());
                }
                cex.exact_init_state(&self.ts);
                let mut line = String::new();
                let mut lbstate = Vec::new();
                for l in cex.state[0].iter() {
                    lbstate.push(Lbool::from(l.polarity()));
                    line.push(if l.polarity() { '1' } else { '0' })
                }
                res.push(line);
                let mut line = String::new();
                for i in cex.input[0].iter() {
                    line.push(if i.polarity() { '1' } else { '0' })
                }
                res.push(line);
                for c in cex.input[1..].iter() {
                    let map: GHashMap<Var, bool> =
                        GHashMap::from_iter(c.iter().map(|l| (l.var(), l.polarity())));
                    let mut line = String::new();
                    let mut input = Vec::new();
                    for l in self.ts.input.iter() {
                        let r = if let Some(r) = map.get(l) { *r } else { true };
                        line.push(if r { '1' } else { '0' });
                        input.push(Lbool::from(r));
                    }
                    res.push(line);
                }
                res.push(".\n".to_string());
                Box::new(res.join("\n"))
            }
        }
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
