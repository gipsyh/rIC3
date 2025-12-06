use crate::{
    Engine,
    config::Config,
    wltransys::{WlTransys, certify::WlWitness, unroll::WlTransysUnroll},
};
use giputils::hash::GHashMap;
use log::{error, info};

pub struct WlKind {
    uts: WlTransysUnroll,
    cfg: Config,
    solver: bitwuzla::Bitwuzla,
    solver_trans_k: usize,
    solver_bad_k: usize,
    owts: WlTransys,
}

impl WlKind {
    pub fn new(cfg: Config, mut wts: WlTransys) -> Self {
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
            info!("kind depth: {k}");
            if k > 0 {
                self.load_bad_to(k - 1);
                let bad_at_k = self.uts.next(&self.uts.ts.bad[0], k);
                if !self.solver.solve(&[bad_at_k]) {
                    info!("k-induction proofed in depth {k}");
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
                info!("bmc found counter-example in depth {k}");
                return Some(false);
            }
        }
        info!("kind reached bound {}, stopping search", self.cfg.end);
        None
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
}
