use crate::transys::Transys;
use logic_form::{VarVMap, simulate::DagCnfSimulation};

impl Transys {
    pub fn frts(&mut self, _rst: &mut VarVMap) {
        dbg!(&self.rel);
        let sim = DagCnfSimulation::new(1, &self.rel);
        dbg!(&sim);
    }
}
