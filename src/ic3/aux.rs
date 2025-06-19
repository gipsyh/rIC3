use crate::{ic3::IC3, transys::TransysIf};
use giputils::{grc::Grc, hash::GHashSet};
use logicrs::{DagCnf, Var};

impl IC3 {
    pub fn add_aux(&mut self, rel: &DagCnf, auxs: &GHashSet<Var>) {
        self.ts.add_aux(rel, auxs);
        self.activity.reserve(self.ts.max_var());
        self.tsctx = Grc::new(self.ts.ctx());
        self.frame.reserve(self.tsctx.max_latch);
    }
}
