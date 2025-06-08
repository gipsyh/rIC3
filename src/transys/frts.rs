use crate::{config::Config, gipsat::DagCnfSolver, transys::Transys};
use giputils::hash::GHashMap;
use logic_form::{VarLMap, VarVMap, simulate::DagCnfSimulation};
use satif::Satif;

impl Transys {
    pub fn frts(&mut self, cfg: &Config, rst: &mut VarVMap) {
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
        for &c in self.constraint.iter() {
            solver.add_clause(&[c]);
        }
        for vs in simval.values().filter(|vs| vs.len() > 1) {
            let m = vs[0];
            for &s in &vs[1..] {
                // dbg!(m, s);
                if !solver.solve(&[m, !s]) && !solver.solve(&[!m, s]) {
                    // dbg!("can replace");
                    replace.insert_lit(s, m);
                }
            }
        }
        // dbg!(&self.max_var());
        self.replace(&replace, rst);
        // dbg!(&self.max_var());
    }
}
