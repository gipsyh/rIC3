use super::IC3;
use crate::transys::TransysIf;
use log::trace;
use logicrs::{Lit, LitOrdVec, LitVec, Var, satif::Satif};
use rand::{Rng, seq::SliceRandom};
use std::time::Instant;

impl IC3 {
    pub(super) fn get_bad(&mut self) -> Option<(LitVec, Vec<LitVec>)> {
        trace!("getting bad state in frame {}", self.level());
        if self.predprop.is_some() {
            self.pred_prop_get_bad()
        } else {
            let start = Instant::now();
            let res = self
                .solvers
                .last_mut()
                .unwrap()
                .solve(&self.tsctx.bad.cube());
            self.statistic.block.get_bad_time += start.elapsed();
            res.then(|| {
                if self.cfg.full_bad {
                    self.get_full_pred(self.solvers.len())
                } else {
                    self.get_pred(self.solvers.len(), true)
                }
            })
        }
    }
}

impl IC3 {
    #[inline]
    #[allow(unused)]
    pub(super) fn sat_contained(&mut self, frame: usize, lemma: &LitOrdVec) -> bool {
        !self.solvers[frame].solve(lemma)
    }

    #[inline]
    #[allow(unused)]
    pub(super) fn blocked(&mut self, frame: usize, cube: &LitVec, strengthen: bool) -> bool {
        self.solvers[frame - 1].inductive(cube, strengthen)
    }

    pub(super) fn blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &LitVec,
        strengthen: bool,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, false);
        self.solvers[frame - 1].inductive(&ordered_cube, strengthen)
    }

    pub(super) fn blocked_with_ordered_with_constrain(
        &mut self,
        frame: usize,
        cube: &LitVec,
        ascending: bool,
        strengthen: bool,
        constraint: Vec<LitVec>,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.solvers[frame - 1].inductive_with_constrain(&ordered_cube, strengthen, constraint)
    }

    pub(super) fn get_pred(&mut self, frame: usize, strengthen: bool) -> (LitVec, Vec<LitVec>) {
        let start = Instant::now();
        let solver = &mut self.solvers[frame - 1];
        let mut cls: LitVec = solver.get_assump().clone();
        let mut cst = self.ts.constraint.clone();
        cls.retain(|l| self.localabs.refine_has(l.var()));
        cst.retain(|l| self.localabs.refine_has(l.var()));
        let order = |mut i: usize, cube: &mut [Lit]| -> bool {
            if self.cfg.inn || !self.auxiliary_var.is_empty() {
                if i == 0 {
                    cube.sort_by(|a, b| b.cmp(a));
                    return true;
                }
                i -= 1;
            }
            match i {
                0 => {
                    self.activity.sort_by_activity(cube, false);
                }
                1 => {
                    if !strengthen {
                        return false;
                    }
                    cube.reverse();
                }
                _ => {
                    cube.shuffle(&mut self.rng);
                }
            };
            true
        };
        let (state, input) = self.lift.lift(solver, cls.iter().chain(cst.iter()), order);
        self.statistic.block.get_pred_time += start.elapsed();
        (state, input)
    }

    pub(super) fn get_full_pred(&mut self, frame: usize) -> (LitVec, Vec<LitVec>) {
        let solver = &mut self.solvers[frame - 1];
        let mut inputs = LitVec::new();
        for input in self.tsctx.input.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            } else {
                inputs.push(lit.not_if(self.rng.random_bool(0.5)));
            }
        }
        let mut latchs = LitVec::new();
        for latch in self.tsctx.latch.iter() {
            let lit = latch.lit();
            if let Some(v) = solver.sat_value(lit) {
                latchs.push(lit.not_if(!v));
            } else {
                latchs.push(lit.not_if(self.rng.random_bool(0.5)));
            }
        }
        (latchs, vec![inputs])
    }

    #[allow(unused)]
    pub(super) fn new_var(&mut self) -> Var {
        let var = self.tsctx.new_var();
        for s in self.solvers.iter_mut() {
            assert!(var == s.new_var());
        }
        todo!();
        // assert!(var == self.lift.new_var());
        var
    }
}
