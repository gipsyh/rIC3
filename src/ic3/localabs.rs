use super::IC3;
use crate::{
    BlWitness,
    ic3::IC3Config,
    transys::{Transys, TransysIf, unroll::TransysUnroll},
};
use giputils::hash::{GHashMap, GHashSet};
use log::{debug, info};
use logicrs::{LitVec, Var, satif::Satif};
use rand::seq::SliceRandom;

pub struct LocalAbs {
    refine: GHashSet<Var>,
    uts: TransysUnroll<Transys>,
    solver: Box<dyn Satif>,
    kslv: usize,
    opt: GHashMap<Var, Var>,
    opt_rev: GHashMap<Var, Var>,
    foundcex: bool,
}

impl LocalAbs {
    pub fn new(ts: &Transys, cfg: &IC3Config) -> Self {
        let mut refine = GHashSet::new();
        refine.insert(Var::CONST);
        refine.extend(ts.bad.iter().map(|l| l.var()));
        if !cfg.abs_cst {
            refine.extend(ts.constraint.iter().map(|l| l.var()))
        }
        if !cfg.abs_trans {
            refine.extend(ts.next.values().map(|l| l.var()));
        }
        let mut uts = TransysUnroll::new(ts);
        if cfg.abs_trans {
            uts.enable_optional_connect();
        }
        if cfg.abs_cst {
            uts.enable_optional_constraint();
        }
        let mut solver: Box<dyn Satif> = Box::new(cadical::CaDiCaL::new());
        uts.load_trans(solver.as_mut(), 0, !cfg.abs_cst);
        uts.ts.load_init(solver.as_mut());
        let opt = uts.opt.clone();
        let opt_rev: GHashMap<Var, Var> = opt.iter().map(|(k, v)| (*v, *k)).collect();
        for r in refine.iter() {
            if let Some(o) = opt.get(r) {
                solver.add_clause(&[o.lit()]);
            }
        }
        Self {
            refine,
            uts,
            solver,
            kslv: 0,
            opt,
            opt_rev,
            foundcex: false,
        }
    }

    pub fn witness(&self) -> Option<BlWitness> {
        if !self.foundcex {
            return None;
        }
        Some(self.uts.witness(self.solver.as_ref()))
    }

    #[inline]
    pub fn refine_has(&self, x: Var) -> bool {
        self.refine.contains(&x)
    }

    fn check(&mut self, mut assumps: LitVec) -> Option<LitVec> {
        let olen = assumps.len();
        assumps.extend(self.uts.lits_next(&self.uts.ts.bad, self.uts.num_unroll));
        if self.solver.solve(&assumps) {
            None
        } else {
            assumps.truncate(olen);
            assumps.retain(|&l| self.solver.unsat_has(l));
            Some(assumps)
        }
    }
}

impl IC3 {
    pub(super) fn check_witness_by_bmc(&mut self, depth: usize) -> bool {
        debug!("localabs: checking witness by bmc with depth {depth}");
        self.localabs.uts.unroll_to(depth);
        for k in self.localabs.kslv + 1..=depth {
            self.localabs
                .uts
                .load_trans(self.localabs.solver.as_mut(), k, !self.cfg.abs_cst);
        }
        self.localabs.kslv = depth;
        let mut assump = LitVec::new();
        for (k, v) in self.localabs.opt.iter() {
            if !self.localabs.refine.contains(k) {
                assump.push(v.lit());
            }
        }
        assump.shuffle(&mut self.rng);
        if let Some(assump) = self.localabs.check(assump) {
            // debug!("checking witness with {} refines", assump.len());
            // let mut i = 0;
            // while i < assump.len() {
            //     let ln = self.localabs.opt_rev[&assump[i].var()];
            //     if self.localabs.refine.contains(&ln) {
            //         i += 1;
            //         continue;
            //     }
            //     let mut drop = assump.clone();
            //     drop.remove(i);
            //     if let Some(drop) = self.localabs.check(drop) {
            //         assump = drop;
            //     } else {
            //         i += 1;
            //     }
            // }
            for l in assump {
                let ln = self.localabs.opt_rev[&l.var()];
                assert!(!self.localabs.refine.contains(&ln));
                self.localabs.refine.insert(ln);
                self.localabs.solver.add_clause(&[l]);
            }
            info!("localabs: refine size: {}", self.localabs.refine.len());
            false
        } else {
            info!("localabs: witness checking passed");
            self.localabs.foundcex = true;
            true
        }
    }
}
