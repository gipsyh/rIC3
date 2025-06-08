mod abc;
pub mod certificate;

use crate::{
    config::{self, Config},
    transys::{Transys, TransysIf},
};
use abc::abc_preprocess;
use aig::{Aig, AigEdge};
use giputils::hash::{GHashMap, GHashSet};
use log::{error, warn};
use logic_form::{Lit, LitVec, Var, VarVMap};
use std::process::exit;

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
            if ts.rel.has_rel(v) {
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
            let init = ts.init.get(l).copied();
            aig.add_latch(map[l].node_id(), next, init.map(AigEdge::constant));
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
                init.insert(lv, i.to_constant());
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

pub fn aig_preprocess(aig: &Aig, cfg: &config::Config) -> (Aig, VarVMap) {
    let (mut aig, mut restore) = aig.coi_refine();
    aig.gate_init_to_constraint();
    if !(cfg.preproc.no_abc || matches!(cfg.engine, config::Engine::IC3) && cfg.ic3.inn) {
        let mut remap_retain = GHashSet::new();
        remap_retain.insert(Var::CONST);
        for i in aig.inputs.iter() {
            remap_retain.insert((*i).into());
        }
        for l in aig.latchs.iter() {
            remap_retain.insert(l.input.into());
        }
        restore.retain(|x, _| remap_retain.contains(x));
        aig = abc_preprocess(aig);
        let remap2;
        (aig, remap2) = aig.coi_refine();
        restore = remap2.product(&restore);
    }
    aig.constraints.retain(|e| !e.is_constant(true));
    (aig, restore)
}

pub struct AigFrontend {
    origin_aig: Aig,
    cfg: Config,
    ts: Transys,
    rst: VarVMap,
}

impl AigFrontend {
    pub fn new(cfg: &Config) -> Self {
        let mut origin_aig = Aig::from_file(&cfg.model);
        if !origin_aig.outputs.is_empty() {
            if origin_aig.bads.is_empty() {
                origin_aig.bads = std::mem::take(&mut origin_aig.outputs);
                warn!(
                    "property not found, moved {} outputs to bad properties",
                    origin_aig.bads.len()
                );
            } else {
                warn!("outputs in aiger are ignored");
                origin_aig.outputs.clear();
            }
        }
        let mut aig = origin_aig.clone();
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
                if let Some(certificate) = &cfg.certificate {
                    let mut map = aig.inputs.clone();
                    map.extend(aig.latchs.iter().map(|l| l.input));
                    for x in map {
                        aig.set_symbol(x, &format!("= {}", x * 2));
                    }
                    aig.to_file(certificate, true);
                }
                println!("RESULT: UNSAT");
                exit(20);
            } else if aig.bads.len() > 1 {
                if cfg.certify || cfg.certificate.is_some() {
                    error!(
                        "multiple properties detected. cannot compress properties when certification is enabled"
                    );
                    panic!();
                }
                warn!(
                    "multiple properties detected. rIC3 has compressed them into a single property"
                );
                aig.compress_property();
            }
        }
        let (aig, rst) = aig_preprocess(&aig, cfg);
        let ts = Transys::from_aig(&aig, true);
        Self {
            origin_aig,
            ts,
            rst,
            cfg: cfg.clone(),
        }
    }

    pub fn is_safety(&self) -> bool {
        if !self.origin_aig.bads.is_empty() {
            true
        } else {
            assert!(!self.ts.justice.is_empty());
            false
        }
    }

    pub fn ts(&mut self) -> Transys {
        self.ts.clone()
    }
}
