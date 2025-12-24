use super::IC3;
use crate::transys::TransysIf;
use giputils::hash::GHashSet;
use log::trace;
use logicrs::{LitOrdVec, LitVec, Var, satif::Satif};
use rand::{Rng, seq::SliceRandom};
use std::time::Instant;

impl IC3 {
    pub(super) fn get_bad(&mut self) -> Option<(LitVec, LitVec)> {
        trace!("getting bad state in frame {}", self.level());
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

impl IC3 {
    #[inline]
    #[allow(unused)]
    pub(super) fn sat_contained(&mut self, frame: usize, lemma: &LitOrdVec) -> bool {
        !self.solvers[frame].solve(lemma)
    }
    
    #[inline]
    #[allow(unused)]
    pub(super) fn blocked(&mut self, frame: usize, cube: &LitVec, strengthen: bool) -> bool {
        self.solvers[frame - 1].inductive(&cube, strengthen)
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

    pub(super) fn get_pred(&mut self, frame: usize, strengthen: bool) -> (LitVec, LitVec) {
        let start = Instant::now();
        let solver = &mut self.solvers[frame - 1];
        let mut cls: LitVec = solver.get_assump().clone();
        cls.extend_from_slice(&self.ts.constraint);
        cls.retain(|l| self.localabs.refine_has(l.var()));
        if cls.is_empty() {
            return (LitVec::new(), LitVec::new());
        }
        let in_cls: GHashSet<Var> = GHashSet::from_iter(cls.iter().map(|l| l.var()));
        let cls = !cls;
        let mut inputs = LitVec::new();
        for input in self.tsctx.input.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        self.lift.set_domain(cls.iter().cloned());
        let mut latchs = LitVec::new();
        for latch in self.tsctx.latch.iter() {
            let lit = latch.lit();
            if self.lift.domain_has(lit.var())
                && let Some(v) = solver.sat_value(lit)
                && (in_cls.contains(latch) || !solver.flip_to_none(*latch))
            {
                latchs.push(lit.not_if(!v));
            }
        }
        let inn: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
            cube.sort_by(|a, b| b.cmp(a));
        });
        let act: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
            self.activity.sort_by_activity(cube, false);
        });
        let rev: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
            cube.reverse();
        });
        let mut order = if self.cfg.inn || !self.auxiliary_var.is_empty() {
            vec![inn, act, rev]
        } else {
            vec![act, rev]
        };
        for i in 0.. {
            if latchs.is_empty() {
                break;
            }
            if let Some(f) = order.get_mut(i) {
                f(&mut latchs);
            } else {
                latchs.shuffle(&mut self.rng);
            }
            let olen = latchs.len();
            latchs = self
                .lift
                .dcs
                .minimal_premise(&inputs, &latchs, &cls)
                .unwrap();
            if latchs.len() == olen || !strengthen {
                break;
            }
        }
        self.lift.unset_domain();
        self.statistic.block.get_pred_time += start.elapsed();
        (latchs, inputs)
    }

    pub(super) fn get_full_pred(&mut self, frame: usize) -> (LitVec, LitVec) {
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
        (latchs, inputs)
    }

    #[allow(unused)]
    pub(super) fn new_var(&mut self) -> Var {
        let var = self.tsctx.new_var();
        for s in self.solvers.iter_mut() {
            assert!(var == s.new_var());
        }
        assert!(var == self.lift.new_var());
        var
    }
}
