use crate::{config::Config, gipsat::DagCnfSolver, transys::Transys};
use giputils::hash::GHashMap;
use logic_form::{VarVMap, simulate::DagCnfSimulation};

impl Transys {
    pub fn frts(&mut self, cfg: &Config, _rst: &mut VarVMap) {
        dbg!(&self.rel.max_var());
        let sim = DagCnfSimulation::new(1, &self.rel);
        let mut simval: GHashMap<_, Vec<_>> = GHashMap::new();
        for v in self.rel.var_iter() {
            let sv = sim[v].clone();
            simval.entry(sv).or_default().push(v);
        }
        let _solver = DagCnfSolver::new(&self.rel, cfg.rseed);
        for _vs in simval.values().filter(|vs| vs.len() > 1) {}
        dbg!(simval);
        dbg!(&sim);
    }
}
