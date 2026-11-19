use crate::{ic3::IC3, transys::TransysIf};
use giputils::{hash::GHashSet, ptr::Grc};
use logicrs::{DagCnf, Var};

impl IC3 {
    pub fn add_aux(&mut self, rel: &DagCnf, auxs: &GHashSet<Var>) {
        self.ts.add_aux(rel, auxs);
        self.activity.extend_to(self.ts.max_var());
        self.tsctx = Grc::new(self.ts.ctx());
        self.frame.extend_to(self.tsctx.max_latch);
    }
}
