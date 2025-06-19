use crate::{ic3::IC3, transys::TransysIf};
use giputils::{grc::Grc, hash::GHashSet};
use logicrs::{DagCnf, LitVec, Var};

impl IC3 {
    // pub fn add_aux(&mut self, aux: Var, rel: Vec<LitVec>) {
    //     for i in 0..trans.len() {
    //         let mut nt = Clause::new();
    //         for l in trans[i].iter() {
    //             nt.push(if l.var() == state {
    //                 next.not_if(!l.polarity())
    //             } else {
    //                 self.ts.lit_next(*l)
    //             });
    //         }
    //         trans.push(nt);
    //     }
    //     self.ts
    //         .add_latch(state, next, init, trans.clone(), dep.clone());
    //     let tmp_lit_set = &mut self.frame.tmp_lit_set;
    //     tmp_lit_set.reserve(self.ts.max_latch);
    //     for s in self.solvers.iter_mut().chain(Some(&mut self.lift)) {
    //         s.reset();
    //         for cls in trans.iter() {
    //             s.add_clause_inner(cls, ClauseKind::Trans);
    //         }
    //         s.add_domain(state, true);
    //     }
    //     if !self.solvers[0].value.v(state.lit()).is_none() {
    //         if self.solvers[0].value.v(state.lit()).is_true() {
    //             self.ts.init.push(state.lit());
    //             self.ts.init_map[state] = Some(true);
    //         } else {
    //             self.ts.init.push(!state.lit());
    //             self.ts.init_map[state] = Some(false);
    //         }
    //     } else if !self.solvers[0].solve_with_domain(&[state.lit()], vec![], true) {
    //         self.ts.init.push(!state.lit());
    //         self.ts.init_map[state] = Some(false);
    //     } else if !self.solvers[0].solve_with_domain(&[!state.lit()], vec![], true) {
    //         self.ts.init.push(state.lit());
    //         self.ts.init_map[state] = Some(true);
    //     }
    //     self.activity.reserve(state);
    //     self.auxiliary_var.push(state);
    // }

    pub fn add_aux(&mut self, rel: &DagCnf, auxs: &GHashSet<Var>) {
        self.ts.add_aux(rel, auxs);
        self.activity.reserve(self.ts.max_var());
        self.tsctx = Grc::new(self.ts.ctx());
    }
}
