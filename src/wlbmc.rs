use crate::{
    Engine,
    config::Config,
    wltransys::{WlTransys, certify::WlWitness, unroll::WlTransysUnroll},
};
use giputils::hash::GHashMap;
use log::info;

pub struct WlBMC {
    cfg: Config,
    #[allow(unused)]
    owts: WlTransys,
    uts: WlTransysUnroll,
    solver: bitwuzla::Bitwuzla,
    solver_k: usize,
}

impl WlBMC {
    pub fn new(cfg: Config, mut wts: WlTransys) -> Self {
        let owts = wts.clone();
        wts.compress_bads();
        let uts = WlTransysUnroll::new(wts);
        let mut solver = bitwuzla::Bitwuzla::new();
        for (l, i) in uts.ts.init.iter() {
            solver.assert(&l.teq(i));
        }
        Self {
            cfg,
            owts,
            uts,
            solver,
            solver_k: 0,
        }
    }

    pub fn load_trans_to(&mut self, k: usize) {
        while self.solver_k < k + 1 {
            for c in self.uts.ts.constraint.iter() {
                self.solver.assert(&self.uts.next(c, self.solver_k));
            }
            self.solver_k += 1;
        }
    }
}

impl Engine for WlBMC {
    fn is_wl(&self) -> bool {
        true
    }

    fn check(&mut self) -> Option<bool> {
        for k in (self.cfg.start..=self.cfg.end).step_by(self.cfg.step as usize) {
            self.uts.unroll_to(k);
            self.load_trans_to(k);
            let assump = self.uts.next(&self.uts.ts.bad[0], k);
            info!("bmc depth: {k}");
            if self.solver.solve(&[assump]) {
                info!("bmc found counter-example in depth {k}");
                return Some(false);
            }
        }
        info!("bmc reached bound {}, stopping search", self.cfg.end);
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
