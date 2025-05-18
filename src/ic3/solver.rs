// use super::IC3;
// use crate::gipsat::ClauseKind;
// use logic_form::{Clause, Cube, Lemma, Lit, Var};
// use rand::seq::SliceRandom;
// use std::{collections::HashSet, time::Instant};

// impl IC3 {
//     pub fn get_bad(&mut self) -> Option<(Cube, Cube)> {
//         self.statistic.num_get_bad += 1;
//         let start = Instant::now();
//         let solver = self.solvers.last_mut().unwrap();
//         solver.assump = self.ts.bad.cube();
//         solver.constrain = Default::default();
//         let res = solver.solve_with_domain(&self.ts.bad.cube(), vec![], false);
//         self.statistic.block_get_bad_time += start.elapsed();
//         if res {
//             let frame = self.solvers.len();
//             Some(self.get_pred(frame, true))
//         } else {
//             None
//         }
//     }
// }

// impl IC3 {
//     pub fn blocked_with_ordered(
//         &mut self,
//         frame: usize,
//         cube: &Cube,
//         ascending: bool,
//         strengthen: bool,
//     ) -> bool {
//         let mut ordered_cube = cube.clone();
//         self.activity.sort_by_activity(&mut ordered_cube, ascending);
//         self.solvers[frame - 1].inductive(&ordered_cube, strengthen)
//     }

//     pub fn blocked_with_ordered_with_constrain(
//         &mut self,
//         frame: usize,
//         cube: &Cube,
//         ascending: bool,
//         strengthen: bool,
//         constrain: Vec<Clause>,
//     ) -> bool {
//         let mut ordered_cube = cube.clone();
//         self.activity.sort_by_activity(&mut ordered_cube, ascending);
//         self.solvers[frame - 1].inductive_with_constrain(&ordered_cube, strengthen, constrain)
//     }

//     pub fn get_pred(&mut self, frame: usize, strengthen: bool) -> (Cube, Cube) {
//         let start = Instant::now();
//         let solver = &mut self.solvers[frame - 1];
//         let mut cls: Cube = solver.assump.clone();
//         cls.extend_from_slice(&self.abs_cst);
//         if cls.is_empty() {
//             return (Cube::new(), Cube::new());
//         }
//         let in_cls: HashSet<Var> = HashSet::from_iter(cls.iter().map(|l| l.var()));
//         let cls = !cls;
//         let mut inputs = Cube::new();
//         for input in self.ts.inputs.iter() {
//             let lit = input.lit();
//             if let Some(v) = solver.sat_value(lit) {
//                 inputs.push(lit.not_if(!v));
//             }
//         }
//         self.lift.set_domain(cls.iter().cloned());
//         let mut latchs = Cube::new();
//         for latch in self.ts.latchs.iter() {
//             let lit = latch.lit();
//             if self.lift.domain.has(lit.var()) {
//                 if let Some(v) = solver.sat_value(lit) {
//                     if in_cls.contains(latch) || !solver.flip_to_none(*latch) {
//                         latchs.push(lit.not_if(!v));
//                     }
//                 }
//             }
//         }
//         let inn: Box<dyn FnMut(&mut Cube)> = Box::new(|cube: &mut Cube| {
//             cube.sort();
//             cube.reverse();
//         });
//         let act: Box<dyn FnMut(&mut Cube)> = Box::new(|cube: &mut Cube| {
//             self.activity.sort_by_activity(cube, false);
//         });
//         let rev: Box<dyn FnMut(&mut Cube)> = Box::new(|cube: &mut Cube| {
//             cube.reverse();
//         });
//         let mut order = if self.options.ic3.inn || !self.auxiliary_var.is_empty() {
//             vec![inn, act, rev]
//         } else {
//             vec![act, rev]
//         };
//         for i in 0.. {
//             if latchs.is_empty() {
//                 break;
//             }
//             if let Some(f) = order.get_mut(i) {
//                 f(&mut latchs);
//             } else {
//                 latchs.shuffle(&mut self.lift.rng);
//             }
//             let olen = latchs.len();
//             latchs = self.lift.minimal_pred(&inputs, &latchs, &cls).unwrap();
//             if latchs.len() == olen || !strengthen {
//                 break;
//             }
//         }
//         self.lift.unset_domain();
//         self.statistic.block_get_predecessor_time += start.elapsed();
//         (latchs, inputs)
//     }
// }

use super::{Frames, IC3};
use crate::transys::Transys;
use giputils::grc::Grc;
use logic_form::{Clause, Cube, Lit};
use satif::Satif;
use std::ops::Deref;

pub type SatSolver = satif_minisat::Solver;

pub struct Ic3Solver {
    solver: Box<SatSolver>,
    ts: Grc<Transys>,
    num_act: usize,
    frame: usize,
    cube: Cube,
    assumption: Cube,
    act: Option<Lit>,
}

impl Ic3Solver {
    pub fn new(ts: &Grc<Transys>, frame: usize) -> Self {
        let ts = ts.clone();
        let mut solver = Box::new(SatSolver::new());
        ts.load_trans(solver.as_mut(), true);
        Self {
            solver,
            ts,
            frame,
            num_act: 0,
            cube: Default::default(),
            assumption: Default::default(),
            act: None,
        }
    }

    pub fn reset(&mut self, frames: &Frames) {
        *self = Self::new(&self.ts, self.frame);
        let frames_slice = if self.frame == 0 {
            &frames[0..1]
        } else {
            &frames[self.frame..]
        };
        for dnf in frames_slice.iter() {
            for cube in dnf.iter() {
                self.add_lemma(&!cube.deref().deref().clone());
            }
        }
    }

    fn finish_last(&mut self) {
        if let Some(act) = self.act {
            self.solver.add_clause(&[act]);
        }
        self.assumption.clear();
        self.cube.clear();
    }

    pub fn add_lemma(&mut self, clause: &Clause) {
        self.finish_last();
        self.solver.add_clause(clause);
    }

    #[allow(unused)]
    pub fn solve(&mut self, assumptions: &[Lit]) -> bool {
        self.finish_last();
        self.solver.solve(assumptions)
    }

    fn inductive(&mut self, cube: &Cube, strengthen: bool) -> bool {
        self.finish_last();
        let mut assumption = self.ts.cube_next(cube);
        if strengthen {
            let act = self.solver.new_var().into();
            assumption.push(act);
            let mut tmp_cls = !cube;
            tmp_cls.push(!act);
            self.solver.add_clause(&tmp_cls);
            let res = self.solver.solve(&assumption);
            let act = !assumption.pop().unwrap();
            self.act = Some(act);
            self.assumption = assumption;
            self.cube = cube.clone();
            !res
        } else {
            let res = self.solver.solve(&assumption);
            self.assumption = assumption;
            self.cube = cube.clone();
            !res
        }
    }

    fn inductive_with_constrain(
        &mut self,
        cube: &Cube,
        strengthen: bool,
        mut constraint: Vec<Clause>,
    ) -> bool {
        self.finish_last();
        let mut assumption = self.ts.cube_next(cube);
        if strengthen || !constraint.is_empty() {
            let act = self.solver.new_var().into();
            assumption.push(act);
            let mut tmp_cls = !cube;
            tmp_cls.push(!act);
            for c in constraint.iter_mut() {
                c.push(!act);
            }
            self.solver.add_clause(&tmp_cls);
            for c in constraint {
                self.solver.add_clause(&c);
            }
            let res = self.solver.solve(&assumption);
            let act = !assumption.pop().unwrap();
            self.act = Some(act);
            self.assumption = assumption;
            self.cube = cube.clone();
            !res
        } else {
            let res = self.solver.solve(&assumption);
            self.assumption = assumption;
            self.cube = cube.clone();
            !res
        }
    }

    pub fn inductive_core(&mut self) -> Cube {
        let mut ans = Cube::new();
        for i in 0..self.cube.len() {
            if self.solver.unsat_has(self.assumption[i]) {
                ans.push(self.cube[i]);
            }
        }
        if self.ts.cube_subsume_init(&ans) {
            ans = Cube::new();
            let new = *self
                .cube
                .iter()
                .find(|l| self.ts.init_map[l.var()].is_some_and(|i| i != l.polarity()))
                .unwrap();
            for i in 0..self.cube.len() {
                if self.solver.unsat_has(self.assumption[i]) || self.cube[i] == new {
                    ans.push(self.cube[i]);
                }
            }
            assert!(!self.ts.cube_subsume_init(&ans));
        }
        ans
    }

    pub fn sat_value(&mut self, lit: Lit) -> Option<bool> {
        self.solver.sat_value(lit)
    }
}

impl IC3 {
    pub fn blocked(&mut self, frame: usize, cube: &Cube, strengthen: bool) -> bool {
        assert!(!self.ts.cube_subsume_init(cube));
        let solver = &mut self.solvers[frame - 1];
        solver.num_act += 1;
        if solver.num_act > 1000 {
            solver.reset(&self.frame);
        }
        let res = self.solvers[frame - 1].inductive(cube, strengthen);
        res
    }

    pub fn blocked_with_constraint(
        &mut self,
        frame: usize,
        cube: &Cube,
        strengthen: bool,
        constraint: Vec<Clause>,
    ) -> bool {
        assert!(!self.ts.cube_subsume_init(cube));
        let solver = &mut self.solvers[frame - 1];
        solver.num_act += 1;
        if solver.num_act > 1000 {
            solver.reset(&self.frame);
        }
        let res = self.solvers[frame - 1].inductive_with_constrain(cube, strengthen, constraint);
        res
    }

    pub fn blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &Cube,
        ascending: bool,
        strengthen: bool,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.blocked(frame, &ordered_cube, strengthen)
    }

    pub fn blocked_with_ordered_with_constrain(
        &mut self,
        frame: usize,
        cube: &Cube,
        ascending: bool,
        strengthen: bool,
        constraint: Vec<Clause>,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.blocked_with_constraint(frame, &ordered_cube, strengthen, constraint)
    }

    pub fn get_bad(&mut self) -> Option<(Cube, Cube)> {
        let solver = self.solvers.last_mut().unwrap();
        solver.finish_last();
        let res = solver.solver.solve(&[self.ts.bad]);
        solver.assumption = self.ts.bad.cube();
        res.then(|| self.get_pred(self.solvers.len()))
    }
}

pub struct Lift {
    solver: SatSolver,
    num_act: usize,
}

impl Lift {
    pub fn new(ts: &Transys) -> Self {
        let mut solver = SatSolver::new();
        ts.load_trans(&mut solver, false);
        Self { solver, num_act: 0 }
    }
}

impl IC3 {
    pub fn get_pred(&mut self, frame: usize) -> (Cube, Cube) {
        self.lift.num_act += 1;
        if self.lift.num_act > 1000 {
            self.lift = Lift::new(&self.ts)
        }
        let solver = &mut self.solvers[frame - 1];
        let act: Lit = self.lift.solver.new_var().into();
        let mut assumption = Cube::from([act]);
        let mut cls = solver.assumption.clone();
        cls.extend_from_slice(&self.ts.constraints);
        cls.push(act);
        let cls = !cls;
        let mut inputs = Cube::new();
        self.lift.solver.add_clause(&cls);
        for input in self.ts.inputs.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        assumption.extend_from_slice(&inputs);
        let mut latchs = Cube::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            match solver.sat_value(lit) {
                Some(true) => latchs.push(lit),
                Some(false) => latchs.push(!lit),
                None => (),
            }
        }
        self.activity.sort_by_activity(&mut latchs, false);
        assumption.extend_from_slice(&latchs);
        let res: Cube = if self.lift.solver.solve(&assumption) {
            panic!()
        } else {
            latchs
                .into_iter()
                .filter(|l| self.lift.solver.unsat_has(*l))
                .collect()
        };
        self.lift.solver.add_clause(&[!act]);
        (res, inputs)
    }
}
