use super::{IC3, proofoblig::ProofObligation};
use crate::transys::{Transys, TransysCtx, TransysIf, unroll::TransysUnroll};
use cadical::Solver;
use giputils::hash::GHashMap;
use log::{debug, error, info};
use logicrs::{Lit, LitVec, Var, satif::Satif};

pub fn verify_invariant(ts: &TransysCtx, invariants: &[LitVec]) -> bool {
    let mut solver = Solver::new();
    ts.load_trans(&mut solver, true);
    ts.load_init(&mut solver);
    for lemma in invariants {
        if solver.solve(lemma) {
            return false;
        }
    }
    let mut solver = Solver::new();
    ts.load_trans(&mut solver, true);
    for lemma in invariants {
        solver.add_clause(&!lemma);
    }
    if solver.solve(&ts.bad.cube()) {
        return false;
    }
    for lemma in invariants {
        if solver.solve(&ts.lits_next(lemma)) {
            return false;
        }
    }
    true
}

impl IC3 {
    pub(super) fn verify(&mut self) {
        if !self.cfg.certify {
            return;
        }
        let invariants = self.frame.invariant();
        if !verify_invariant(&self.tsctx, &invariants) {
            error!("invariant varify failed");
            panic!();
        }
        info!(
            "inductive invariant verified with {} lemmas!",
            invariants.len()
        );
    }

    fn check_witness_with_constrain<S: Satif + ?Sized>(
        &mut self,
        solver: &mut S,
        uts: &TransysUnroll<Transys>,
        mut assumps: LitVec,
    ) -> Option<LitVec> {
        let olen = assumps.len();
        assumps.extend(uts.lits_next(&uts.ts.bad, uts.num_unroll));
        if solver.solve(&assumps) {
            None
        } else {
            assumps.truncate(olen);
            // assumps.retain(|&l| solver.unsat_has(l));
            Some(assumps)
        }
    }

    pub(super) fn check_witness_by_bmc(&mut self, b: ProofObligation) -> Option<Vec<Var>> {
        debug!("checking witness by bmc with depth {}", b.depth);
        let mut uts = TransysUnroll::new(&self.ts);
        if self.cfg.ic3.abs_trans {
            uts.enable_optional_connect();
        }
        uts.unroll_to(b.depth);
        let mut solver: Box<dyn Satif> = Box::new(cadical::Solver::new());
        for k in 0..=b.depth {
            uts.load_trans(solver.as_mut(), k, !self.cfg.ic3.abs_cst);
        }
        uts.ts.load_init(solver.as_mut());
        let mut opt_cst = GHashMap::new();
        if self.cfg.ic3.abs_cst {
            for c in uts.ts.constraint.clone() {
                let cc = uts.new_var();
                opt_cst.insert(c, cc);
                for k in 0..=b.depth {
                    solver.add_clause(&[!cc.lit(), uts.lit_next(c, k)]);
                }
            }
        }
        let opt_cst_rev: GHashMap<Var, Lit> = opt_cst.iter().map(|(k, v)| (*v, *k)).collect();
        let mut assump: LitVec = opt_cst.values().map(|l| l.lit()).collect();
        let mut opt_latch = GHashMap::new();
        if let Some((connect, _)) = uts.connect.as_ref() {
            opt_latch = connect.clone();
        }
        let opt_latch_rev: GHashMap<Var, Var> = opt_latch.iter().map(|(k, v)| (*v, *k)).collect();
        assump.extend(opt_latch.values().map(|l| l.lit()));
        if let Some(mut assump) = self.check_witness_with_constrain(solver.as_mut(), &uts, assump) {
            let mut i = 0;
            while i < assump.len() {
                if let Some(ln) = opt_latch_rev.get(&assump[i].var()) {
                    if self.local_abs.contains(ln) {
                        i += 1;
                        continue;
                    }
                } else {
                    let cst = opt_cst_rev.get(&assump[i].var()).unwrap();
                    if self.local_abs.contains(&cst.var()) {
                        i += 1;
                        continue;
                    }
                }
                let mut drop = assump.clone();
                drop.remove(i);
                if let Some(_) =
                    self.check_witness_with_constrain(solver.as_mut(), &uts, drop.clone())
                {
                    assump = drop;
                } else {
                    i += 1;
                }
            }
            let mut res = Vec::new();
            for l in assump {
                if let Some(ln) = opt_latch_rev.get(&l.var()) {
                    if !self.local_abs.contains(ln) {
                        res.push(*ln);
                    }
                } else if let Some(c) = opt_cst_rev.get(&l.var()) {
                    if !self.local_abs.contains(&c.var()) {
                        res.push(c.var());
                    }
                } else {
                    unreachable!();
                }
            }
            assert!(!res.is_empty());
            Some(res)
        } else {
            info!("witness checking passed");
            self.bmc_solver = Some((solver, uts));
            None
        }
    }
}
