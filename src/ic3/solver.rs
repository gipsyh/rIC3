use super::IC3;
use giputils::hash::GHashSet;
use logic_form::{LitOrdVec, LitVec, Var};
use rand::{Rng, seq::SliceRandom};
use satif::Satif;
use std::time::Instant;

impl IC3 {
    pub(super) fn get_bad(&mut self) -> Option<(LitVec, Vec<LitVec>, usize)> {
        self.statistic.num_get_bad += 1;
        let start = Instant::now();
        if !self.cfg.ic3.no_pred_prop {
            assert!(!self.cfg.ic3.full_bad);
            let res = self.bad_solver.solve(&self.bad_ts.bad.cube());
            self.statistic.block_get_bad_time += start.elapsed();
            res.then(|| {
                let (s, i) =
                    self.bad_lift
                        .get_pred(&self.bad_solver, &self.bad_ts.bad.cube(), true);
                let mut input = vec![LitVec::default(); 2];
                for i in i {
                    if let Some(bi) = self.bad_input.get(&i.var()) {
                        input[1].push(i.map_var(|_| *bi));
                    } else {
                        input[0].push(i);
                    }
                }
                (s, input, 1)
            })
        } else {
            let res = self.solvers.last_mut().unwrap().solve(&self.ts.bad.cube());
            self.statistic.block_get_bad_time += start.elapsed();
            res.then(|| {
                if self.cfg.ic3.full_bad {
                    self.get_full_pred(self.solvers.len())
                } else {
                    self.get_pred(self.solvers.len(), true)
                }
            })
            .map(|(s, i)| (s, vec![i], 0))
        }
    }
}

impl IC3 {
    #[inline]
    #[allow(unused)]
    pub(super) fn sat_contained(&mut self, frame: usize, lemma: &LitOrdVec) -> bool {
        !self.solvers[frame].solve(lemma)
    }

    pub(super) fn blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &LitVec,
        ascending: bool,
        strengthen: bool,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
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
        cls.extend_from_slice(&self.abs_cst);
        if cls.is_empty() {
            return (LitVec::new(), LitVec::new());
        }
        let in_cls: GHashSet<Var> = GHashSet::from_iter(cls.iter().map(|l| l.var()));
        let cls = !cls;
        let mut inputs = LitVec::new();
        for input in self.ts.inputs.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        self.lift.set_domain(cls.iter().cloned());
        let mut latchs = LitVec::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            if self.lift.domain_has(lit.var())
                && let Some(v) = solver.sat_value(lit)
                && (in_cls.contains(latch) || !solver.flip_to_none(*latch))
            {
                latchs.push(lit.not_if(!v));
            }
        }
        let inn: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
            cube.sort();
            cube.reverse();
        });
        let act: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
            self.activity.sort_by_activity(cube, false);
        });
        let rev: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
            cube.reverse();
        });
        let mut order = if self.cfg.ic3.inn || !self.auxiliary_var.is_empty() {
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
            latchs = self.lift.minimal_pred(&inputs, &latchs, &cls).unwrap();
            if latchs.len() == olen || !strengthen {
                break;
            }
        }
        self.lift.unset_domain();
        self.statistic.block_get_predecessor_time += start.elapsed();
        (latchs, inputs)
    }

    pub(super) fn get_full_pred(&mut self, frame: usize) -> (LitVec, LitVec) {
        let solver = &mut self.solvers[frame - 1];
        let mut inputs = LitVec::new();
        for input in self.ts.inputs.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            } else {
                inputs.push(lit.not_if(self.rng.random_bool(0.5)));
            }
        }
        let mut latchs = LitVec::new();
        for latch in self.ts.latchs.iter() {
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
        let var = self.ts.new_var();
        for s in self.solvers.iter_mut() {
            assert!(var == s.new_var());
        }
        assert!(var == self.lift.new_var());
        var
    }
}
