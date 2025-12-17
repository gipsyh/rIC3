use crate::{
    Engine,
    config::EngineConfigBase,
    tracer::{Tracer, TracerIf},
    wltransys::{
        WlTransys,
        certify::{WlProof, WlWitness},
        unroll::WlTransysUnroll,
    },
};
use clap::Args;
use giputils::hash::GHashMap;
use log::{error, info};
use logicrs::fol::{Sort, Term, op};
use serde::{Deserialize, Serialize};
use std::ops::Deref;

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct WlKindConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,
}

impl Deref for WlKindConfig {
    type Target = EngineConfigBase;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

pub struct WlKind {
    uts: WlTransysUnroll,
    cfg: WlKindConfig,
    solver: bitwuzla::Bitwuzla,
    solver_trans_k: usize,
    solver_bad_k: usize,
    owts: WlTransys,
    tracer: Tracer,
}

impl WlKind {
    pub fn new(cfg: WlKindConfig, mut wts: WlTransys) -> Self {
        let owts = wts.clone();
        wts.compress_bads();
        let uts = WlTransysUnroll::new(wts);
        let solver = bitwuzla::Bitwuzla::new();
        Self {
            uts,
            cfg,
            solver,
            solver_trans_k: 0,
            solver_bad_k: 0,
            owts,
            tracer: Tracer::new(),
        }
    }

    pub fn load_trans_to(&mut self, k: usize) {
        while self.solver_trans_k < k + 1 {
            for c in self.uts.ts.constraint.iter() {
                self.solver.assert(&self.uts.next(c, self.solver_trans_k));
            }
            self.solver_trans_k += 1;
        }
    }

    pub fn load_bad_to(&mut self, k: usize) {
        while self.solver_bad_k < k + 1 {
            if !self.uts.ts.bad.is_empty() {
                let bad_at_k = self.uts.next(&self.uts.ts.bad[0], self.solver_bad_k);
                self.solver.assert(&!bad_at_k);
            }
            self.solver_bad_k += 1;
        }
    }
}

impl Engine for WlKind {
    fn is_wl(&self) -> bool {
        true
    }

    fn check(&mut self) -> Option<bool> {
        let step = self.cfg.step as usize;
        if step != 1 {
            error!("k-induction step should be 1, got {step}");
            panic!();
        }
        if self.cfg.start != 0 {
            error!("k-induction start should be 0, got {}", self.cfg.start);
            panic!();
        }
        for k in 0..=self.cfg.end {
            self.uts.unroll_to(k);
            self.load_trans_to(k);
            if k > 0 {
                self.load_bad_to(k - 1);
                let bad_at_k = self.uts.next(&self.uts.ts.bad[0], k);
                if !self.solver.solve(&[bad_at_k]) {
                    self.tracer.trace_res(crate::McResult::Safe);
                    return Some(true);
                }
            }

            let mut assump = Vec::new();
            for (l, i) in self.uts.ts.init.iter() {
                assump.push(self.uts.next(l, 0).teq(i));
            }
            let bad_at_k = self.uts.next(&self.uts.ts.bad[0], k);
            assump.push(bad_at_k);

            if self.solver.solve(&assump) {
                self.tracer.trace_res(crate::McResult::Unsafe(k));
                return Some(false);
            }
            self.tracer.trace_res(crate::McResult::Unknown(Some(k)));
        }
        info!("kind reached bound {}, stopping search", self.cfg.end);
        None
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn wl_witness(&mut self) -> WlWitness {
        let mut witness = self.uts.witness(&mut self.solver);
        let mut cache = GHashMap::new();
        let mut ilmap = GHashMap::new();
        for i in self.owts.input.iter().chain(self.owts.latch.iter()) {
            ilmap.insert(i, self.uts.next(i, self.uts.num_unroll));
        }
        let bads: Vec<_> = self
            .owts
            .bad
            .iter()
            .map(|b| b.cached_apply(&|t| ilmap.get(t).cloned(), &mut cache))
            .collect();
        witness.bad_id = bads
            .into_iter()
            .position(|b| self.solver.sat_value(&b).is_some_and(|v| v.bool()))
            .unwrap();
        witness
    }

    fn wl_proof(&mut self) -> WlProof {
        let mut proof = self.uts.ts.clone();
        let mut up = WlTransysUnroll::new(proof.clone());
        up.enable_new_next_latch();
        up.unroll_to(self.uts.num_unroll);
        let bad = proof.bad[0].clone();
        let mut bads = Vec::new();
        for k in 0..up.num_unroll {
            let mut ors = vec![up.next(&bad, k)];
            for c in proof.constraint.iter() {
                ors.push(!up.next(c, k));
            }
            bads.push(Term::new_op_fold(op::Or, ors));
        }
        let mut aux_vars = Vec::new();
        for k in 0..up.num_unroll {
            let aux = Term::new_var(Sort::bool());
            aux_vars.push(aux.clone());
            let (init, next) = if k == 0 {
                (Some(Term::bool_const(true)), aux.clone())
            } else {
                (Some(Term::bool_const(false)), aux_vars[k - 1].clone())
            };
            proof.add_latch(aux, init, next);
        }

        for k in 1..up.num_unroll {
            for v in up.ts.input.iter().chain(up.ts.latch.iter()) {
                let current = up.next(v, k);
                let prev = up.next(v, k - 1);
                proof.add_latch(current.clone(), None, prev.clone());
            }
        }
        for i in 0..bads.len() {
            bads[i] = !(aux_vars[i].imply(!&bads[i]));
        }
        for k in 1..up.num_unroll {
            let al = aux_vars[k].clone();
            let al_next = aux_vars[k - 1].clone();
            let p = al.imply(&al_next);
            bads.push(!p);
            let mut eqs = Vec::new();
            for l in up.ts.latch.iter() {
                let l_next = up.ts.next(l);
                let l_next_k = up.next(&l_next, k);
                let l_ks1 = up.next(l, k - 1);
                eqs.push(l_next_k.teq(&l_ks1));
            }
            let p = al.imply(Term::new_op_fold(op::And, eqs));
            bads.push(!p);
            let mut init = Vec::new();
            for (l, init_val) in up.ts.init.iter() {
                let l_ks1 = up.next(l, k - 1);
                let init_val = up.apply_next(init_val, k - 1);
                init.push(l_ks1.teq(init_val));
            }
            let init = Term::new_op_fold(op::And, init);
            bads.push(!((!al & al_next).imply(&init)))
        }
        bads.push(!&aux_vars[0]);
        proof.bad = vec![Term::new_op_fold(op::Or, bads)];
        WlProof { proof }
    }
}
