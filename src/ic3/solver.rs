use super::IC3;
use crate::transys::TransysIf;
use log::trace;
use logicrs::{Lit, LitOrdVec, LitVec, Var, satif::Satif};
use rand::{RngExt, seq::SliceRandom};
use std::time::Instant;

pub(super) struct Blocked<'a, 'cube> {
    ic3: &'a mut IC3,
    frame: usize,
    cube: &'cube LitVec,
    order: BlockedOrder,
    strengthen: bool,
    constraint: Vec<LitVec>,
}

#[derive(Default)]
enum BlockedOrder {
    Activity {
        ascending: bool,
    },
    #[allow(unused)]
    Inn,
    #[default]
    None,
}

impl<'a, 'cube> Blocked<'a, 'cube> {
    pub(super) fn with_act_order(mut self, ascending: bool) -> Self {
        self.order = BlockedOrder::Activity { ascending };
        self
    }

    #[allow(unused)]
    pub(super) fn with_inn_order(mut self) -> Self {
        self.order = BlockedOrder::Inn;
        self
    }

    pub(super) fn with_strengthen(mut self) -> Self {
        self.strengthen = true;
        self
    }

    pub(super) fn with_constraint(mut self, constraint: &[LitVec]) -> Self {
        self.constraint = constraint.to_vec();
        self
    }

    pub(super) fn check(self) -> bool {
        let Self {
            ic3,
            frame,
            cube,
            order,
            strengthen,
            constraint,
        } = self;

        let ordered_cube = match order {
            BlockedOrder::Activity { ascending } => {
                let mut ordered = cube.clone();
                ic3.activity.sort_by_activity(&mut ordered, ascending);
                Some(ordered)
            }
            BlockedOrder::Inn => {
                let mut ordered = cube.clone();
                ordered.sort_by(|a, b| ic3.inn_cmp(b, a));
                Some(ordered)
            }
            BlockedOrder::None => None,
        };
        let cube = ordered_cube
            .as_ref()
            .map(|cube| cube.as_slice())
            .unwrap_or_else(|| cube.as_slice());
        ic3.solvers[frame - 1].inductive_with_constrain(cube, strengthen, constraint)
    }
}

impl IC3 {
    pub(super) fn get_bad(&mut self) -> Option<(LitVec, Vec<LitVec>)> {
        trace!("getting bad state in frame {}", self.level());
        if self.predprop.is_some() {
            self.pred_prop_get_bad()
        } else {
            let start = Instant::now();
            assert!(self.tsctx.bad.len() == 1);
            let res = self.solvers.last_mut().unwrap().solve(&[self.tsctx.bad[0]]);
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

    pub(super) fn blocked<'cube>(
        &mut self,
        frame: usize,
        cube: &'cube LitVec,
    ) -> Blocked<'_, 'cube> {
        Blocked {
            ic3: self,
            frame,
            cube,
            order: BlockedOrder::default(),
            strengthen: false,
            constraint: Vec::new(),
        }
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
                    cube.sort_by(|a, b| {
                        self.ts_top_lv[b]
                            .cmp(&self.ts_top_lv[a])
                            .then_with(|| self.activity.cmp(b, a))
                    });
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
