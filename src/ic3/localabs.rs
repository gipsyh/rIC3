use super::IC3;
use crate::{
    Witness,
    config::Config,
    transys::{Transys, TransysIf, unroll::TransysUnroll},
};
use giputils::hash::{GHashMap, GHashSet};
use log::{debug, info};
use logicrs::{LitVec, Var, VarVMap, satif::Satif};

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
    pub fn new(ts: &Transys, cfg: &Config) -> Self {
        let mut refine = GHashSet::new();
        refine.insert(Var::CONST);
        refine.extend(ts.bad.iter().map(|l| l.var()));
        if !cfg.ic3.abs_cst {
            refine.extend(ts.constraint.iter().map(|l| l.var()))
        }
        if !cfg.ic3.abs_trans {
            refine.extend(ts.next.values().map(|l| l.var()));
        }
        let mut uts = TransysUnroll::new(ts);
        if cfg.ic3.abs_trans {
            uts.enable_optional_connect();
        }
        if cfg.ic3.abs_cst {
            uts.enable_optional_constraint();
        }
        let mut solver: Box<dyn Satif> = Box::new(cadical::Solver::new());
        uts.load_trans(solver.as_mut(), 0, !cfg.ic3.abs_cst);
        uts.ts.load_init(solver.as_mut());

        let mut opt = GHashMap::new();
        if let Some((connect, _)) = uts.connect.as_ref() {
            opt = connect.clone();
        }
        if let Some((copt, _)) = uts.optcst.as_ref() {
            for (k, v) in copt.iter() {
                opt.insert(*k, *v);
            }
        }
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

    pub fn witness(&self, rst: &VarVMap) -> Option<Witness> {
        if !self.foundcex {
            return None;
        }
        let mut res = Witness::default();
        for k in 0..=self.uts.num_unroll {
            let mut w = LitVec::new();
            for l in self.uts.ts.input() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl)
                    && let Some(r) = rst.lit_map(l.not_if(!v))
                {
                    w.push(r);
                }
            }
            res.input.push(w);
            let mut w = LitVec::new();
            for l in self.uts.ts.latch() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl)
                    && let Some(r) = rst.lit_map(l.not_if(!v))
                {
                    w.push(r);
                }
            }
            res.state.push(w);
        }
        return Some(res);
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
        debug!("localabs: checking witness by bmc with depth {}", depth);
        self.localabs.uts.unroll_to(depth);
        for k in self.localabs.kslv + 1..=depth {
            self.localabs
                .uts
                .load_trans(self.localabs.solver.as_mut(), k, !self.cfg.ic3.abs_cst);
        }
        self.localabs.kslv = depth;
        let mut assump = LitVec::new();
        for (k, v) in self.localabs.opt.iter() {
            if !self.localabs.refine.contains(k) {
                assump.push(v.lit());
            }
        }
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
