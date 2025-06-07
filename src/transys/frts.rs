use crate::transys::Transys;
use giputils::hash::GHashMap;
use logic_form::{VarVMap, simulate::DagCnfSimulation};

impl Transys {
    pub fn frts(&mut self, _rst: &mut VarVMap) {
        dbg!(&self.rel.max_var());
        let sim = DagCnfSimulation::new(1, &self.rel);
        let mut simval: GHashMap<_, Vec<_>> = GHashMap::new();
        for v in self.rel.var_iter() {
            let sv = sim[v].clone();
            simval.entry(sv).or_default().push(v);
        }
        dbg!(simval);
        dbg!(&sim);
    }
}
