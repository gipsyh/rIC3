use crate::{
    config::Config,
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf},
};
use giputils::hash::GHashMap;
use log::info;
use logic_form::{LitVec, VarLMap, VarVMap, simulate::DagCnfSimulation};
use satif::Satif;
use std::time::{Duration, Instant};

impl Transys {
    pub fn frts(&mut self, cfg: &Config, rst: &mut VarVMap) {
        let start = Instant::now();
        let sim = DagCnfSimulation::new(1, &self.rel);
        let mut simval: GHashMap<_, Vec<_>> = GHashMap::new();
        for v in self.rel.var_iter() {
            let lv = v.lit();
            let slv = sim.val(lv);
            let snlv = sim.val(!lv);
            if let Some(e) = simval.get_mut(&slv) {
                e.push(lv);
            } else if let Some(e) = simval.get_mut(&snlv) {
                e.push(!lv);
            } else {
                simval.insert(slv, vec![lv]);
            }
        }
        let mut replace = VarLMap::new();
        let mut solver = DagCnfSolver::new(&self.rel, cfg.rseed);
        // for &c in self.constraint.iter() {
        //     solver.add_clause(&[c]);
        // }
        let limit = Duration::from_millis(500);
        for vs in simval.values().filter(|vs| vs.len() > 1) {
            let m = vs[0];
            for &s in &vs[1..] {
                // dbg!(m, s);
                if let Some(false) = solver.solve_with_limit(
                    &[],
                    vec![LitVec::from([m, s]), LitVec::from([!m, !s])],
                    limit,
                ) {
                    // dbg!("can replace");
                    replace.insert_lit(s, m);
                }
            }
        }
        // for c in self.constraint.iter() {
        //     dbg!(replace.map_lit(*c));
        // }
        let before = self.max_var();
        self.replace(&replace, rst);
        info!(
            "frts eliminates {} out of {} vars in {:.2}s.",
            *before - *self.max_var(),
            *before,
            start.elapsed().as_secs_f32()
        );
    }
}
