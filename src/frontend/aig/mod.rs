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
use logic_form::{Lit, LitVec, Var};
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
            aig.add_latch(map[l].node_id(), next, init);
        }
        aig.bads.push(map_lit(ts.bad));
        for c in ts.constraint() {
            aig.constraints.push(map_lit(c));
        }
        aig.justice = vec![ts.justice.iter().map(|&j| map_lit(j)).collect()];
        for &f in ts.fairness.iter() {
            aig.fairness.push(map_lit(f));
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
                init.insert(lv, i);
            }
        }
        let bad = aig
            .bads
            .first()
            .map_or(Lit::constant(false), |e| e.to_lit());
        let constraint: LitVec = aig.constraints.iter().map(|c| c.to_lit()).collect();
        let justice = aig
            .justice
            .first()
            .map(|j| j.iter().map(|e| e.to_lit()).collect())
            .unwrap_or_default();
        let fairness: LitVec = aig.fairness.iter().map(|f| f.to_lit()).collect();
        let rel = aig.cnf(compact);
        let mut rst = GHashMap::new();
        for v in Var::CONST..=rel.max_var() {
            rst.insert(v, v);
        }
        Transys {
            input,
            latch,
            next,
            init,
            bad,
            constraint,
            justice,
            fairness,
            rel,
            rst,
        }
    }
}

pub fn aig_preprocess(aig: &Aig, options: &config::Config) -> (Aig, GHashMap<Var, Var>) {
    let (mut aig, mut remap) = aig.coi_refine();
    if !(options.preprocess.no_abc
        || matches!(options.engine, config::Engine::IC3) && options.ic3.inn)
    {
        let mut remap_retain = GHashSet::new();
        remap_retain.insert(Var::CONST);
        for i in aig.inputs.iter() {
            remap_retain.insert((*i).into());
        }
        for l in aig.latchs.iter() {
            remap_retain.insert(l.input.into());
        }
        remap.retain(|x, _| remap_retain.contains(x));
        aig = abc_preprocess(aig);
        let remap2;
        (aig, remap2) = aig.coi_refine();
        remap = {
            let mut remap_final = GHashMap::new();
            for (x, y) in remap2 {
                if let Some(z) = remap.get(&y) {
                    remap_final.insert(x, *z);
                }
            }
            remap_final
        }
    }
    aig.constraints.retain(|e| !e.is_constant(true));
    (aig, remap)
}

pub struct AigFrontend {
    origin_aig: Aig,
    opt: Config,
    ts: Transys,
}

impl AigFrontend {
    pub fn new(opt: &Config) -> Self {
        let mut origin_aig = Aig::from_file(&opt.model);
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
            if opt.certify || opt.certificate.is_some() {
                error!("rIC3 does not support solving liveness property with certificate");
                panic!();
            }
        } else {
            if !aig.fairness.is_empty() {
                warn!("fairness constraints are ignored when solving the safety property");
                aig.fairness.clear();
            }
            if aig.bads.is_empty() {
                warn!("no property to be checked");
                if let Some(certificate) = &opt.certificate {
                    aig.to_file(certificate, true);
                }
                exit(20);
            } else if aig.bads.len() > 1 {
                if opt.certify || opt.certificate.is_some() {
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
        let (aig, rst) = aig_preprocess(&aig, opt);
        let mut ts = Transys::from_aig(&aig, true);
        ts.rst = rst;
        if opt.l2s {
            ts = ts.l2s();
        }
        Self {
            origin_aig,
            ts,
            opt: opt.clone(),
        }
    }

    pub fn ts(&mut self) -> Transys {
        self.ts.clone()
    }
}
