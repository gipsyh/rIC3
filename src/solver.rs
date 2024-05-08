use super::Frames;
use crate::{model::Model, Ic3};
use logic_form::{Clause, Cube, Lit};
use satif::{SatResult, Satif, SatifSat, SatifUnsat};
use std::{mem::take, ops::Deref, time::Instant};

pub type SatSolver = minisat::Solver;
type Sat = minisat::Sat;
type Unsat = minisat::Unsat;

pub struct Ic3Solver {
    solver: Box<SatSolver>,
    num_act: usize,
    frame: usize,
    temporary: Vec<Cube>,
}

impl Ic3Solver {
    pub fn new(model: &Model, frame: usize) -> Self {
        let mut solver = Box::new(SatSolver::new());
        let false_lit: Lit = solver.new_var().into();
        solver.add_clause(&[!false_lit]);
        model.load_trans(&mut solver);
        Self {
            solver,
            frame,
            num_act: 0,
            temporary: Vec::new(),
        }
    }

    pub fn reset(&mut self, model: &Model, frames: &Frames) {
        let temporary = take(&mut self.temporary);
        *self = Self::new(model, self.frame);
        for t in temporary {
            self.solver.add_clause(&!&t);
            self.temporary.push(t);
        }
        let frames_slice = if self.frame == 0 {
            &frames[0..1]
        } else {
            &frames[self.frame..]
        };
        for dnf in frames_slice.iter() {
            for cube in dnf {
                self.add_clause(&!cube.deref());
            }
        }
    }

    pub fn add_clause(&mut self, clause: &Clause) {
        let mut cube = !clause;
        cube.sort_by_key(|x| x.var());
        let temporary = take(&mut self.temporary);
        for t in temporary {
            if !cube.ordered_subsume(&t) {
                self.temporary.push(t);
            }
        }
        self.solver.add_clause(clause);
    }

    #[allow(unused)]
    pub fn solve(&mut self, assumptions: &[Lit]) -> SatResult<Sat, Unsat> {
        self.solver.solve(assumptions)
    }
}

impl Ic3 {
    fn blocked_inner(&mut self, frame: usize, cube: &Cube, strengthen: bool) -> BlockResult {
        self.statistic.num_sat_inductive += 1;
        let solver_idx = frame - 1;
        let solver = &mut self.solvers[solver_idx].solver;
        let start = Instant::now();
        let mut assumption = self.model.cube_next(cube);
        let sat_start = Instant::now();
        let res = if strengthen {
            let act = solver.new_var().into();
            assumption.push(act);
            let mut tmp_cls = !cube;
            tmp_cls.push(!act);
            solver.add_clause(&tmp_cls);
            let res = solver.solve(&assumption);
            let act = !assumption.pop().unwrap();
            match res {
                SatResult::Sat(sat) => BlockResult::No(BlockResultNo {
                    sat,
                    solver: solver.as_mut(),
                    assumption,
                    act: Some(act),
                }),
                SatResult::Unsat(unsat) => BlockResult::Yes(BlockResultYes {
                    unsat,
                    solver: solver.as_mut(),
                    cube: cube.clone(),
                    assumption,
                    act: Some(act),
                }),
            }
        } else {
            match solver.solve(&assumption) {
                SatResult::Sat(sat) => BlockResult::No(BlockResultNo {
                    sat,
                    solver: solver.as_mut(),
                    assumption,
                    act: None,
                }),
                SatResult::Unsat(unsat) => BlockResult::Yes(BlockResultYes {
                    unsat,
                    solver: solver.as_mut(),
                    cube: cube.clone(),
                    assumption,
                    act: None,
                }),
            }
        };
        self.statistic.avg_sat_call_time += sat_start.elapsed();
        self.statistic.sat_inductive_time += start.elapsed();
        res
    }

    pub fn blocked(&mut self, frame: usize, cube: &Cube, strengthen: bool) -> BlockResult {
        assert!(!self.model.cube_subsume_init(cube));
        let solver = &mut self.solvers[frame - 1];
        solver.num_act += 1;
        if solver.num_act > 1000 {
            self.statistic.num_solver_restart += 1;
            solver.reset(&self.model, &self.frames);
        }
        self.blocked_inner(frame, cube, strengthen)
    }

    pub fn blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &Cube,
        ascending: bool,
        strengthen: bool,
    ) -> BlockResult {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.blocked(frame, &ordered_cube, strengthen)
    }

    pub fn get_bad(&mut self) -> Option<Cube> {
        let solver = self.solvers.last_mut().unwrap();
        self.statistic.qbad_num += 1;
        let qtarget_start = self.statistic.time.start();
        let res = match solver.solver.solve(&self.model.bad) {
            SatResult::Sat(sat) => Some(BlockResultNo {
                sat,
                assumption: self.model.bad.clone(),
                solver: solver.solver.as_mut(),
                act: None,
            }),
            SatResult::Unsat(_) => None,
        };
        self.statistic.qbad_avg_time += self.statistic.time.stop(qtarget_start);
        res.map(|res| self.unblocked_model(res))
    }
}

pub enum BlockResult {
    Yes(BlockResultYes),
    No(BlockResultNo),
}

pub struct BlockResultYes {
    unsat: Unsat,
    solver: *mut SatSolver,
    cube: Cube,
    assumption: Cube,
    act: Option<Lit>,
}

impl Drop for BlockResultYes {
    fn drop(&mut self) {
        if let Some(act) = self.act {
            let solver = unsafe { &mut *self.solver };
            solver.add_clause(&[act]);
        }
    }
}

pub struct BlockResultNo {
    sat: Sat,
    solver: *mut SatSolver,
    assumption: Cube,
    act: Option<Lit>,
}

impl BlockResultNo {
    pub fn lit_value(&self, lit: Lit) -> Option<bool> {
        self.sat.lit_value(lit)
    }
}

impl Drop for BlockResultNo {
    fn drop(&mut self) {
        if let Some(act) = self.act {
            let solver = unsafe { &mut *self.solver };
            solver.add_clause(&[act]);
        }
    }
}

impl Ic3 {
    pub fn blocked_conflict(&mut self, block: BlockResultYes) -> Cube {
        // let mut ans = Cube::new();
        // for i in 0..block.cube.len() {
        //     if block.unsat.has(block.assumption[i]) {
        //         ans.push(block.cube[i]);
        //     }
        // }
        // if self.model.cube_subsume_init(&ans) {
        //     ans = Cube::new();
        //     let new = *block
        //         .cube
        //         .iter()
        //         .find(|l| {
        //             self.model
        //                 .init_map
        //                 .get(&l.var())
        //                 .is_some_and(|i| *i != l.polarity())
        //         })
        //         .unwrap();
        //     for i in 0..block.cube.len() {
        //         if block.unsat.has(block.assumption[i]) || block.cube[i] == new {
        //             ans.push(block.cube[i]);
        //         }
        //     }
        //     assert!(!self.model.cube_subsume_init(&ans));
        // }
        // ans
        todo!()
    }

    pub fn unblocked_model(&mut self, unblock: BlockResultNo) -> Cube {
        self.statistic.qlift_num += 1;
        let qlift_start = self.statistic.time.start();
        let res = self.minimal_predecessor(unblock);
        self.statistic.qlift_avg_time += self.statistic.time.stop(qlift_start);
        res
    }
}

pub struct Lift {
    solver: SatSolver,
    num_act: usize,
}

impl Lift {
    pub fn new(model: &Model) -> Self {
        let mut solver = SatSolver::new();
        let false_lit: Lit = solver.new_var().into();
        solver.add_clause(&[!false_lit]);
        model.load_trans(&mut solver);
        Self { solver, num_act: 0 }
    }
}

impl Ic3 {
    pub fn minimal_predecessor(&mut self, unblock: BlockResultNo) -> Cube {
        let start = Instant::now();
        self.lift.num_act += 1;
        if self.lift.num_act > 1000 {
            self.lift = Lift::new(&self.model)
        }
        let act: Lit = self.lift.solver.new_var().into();
        let mut assumption = Cube::from([act]);
        let mut cls = !&unblock.assumption;
        cls.push(!act);
        self.lift.solver.add_clause(&cls);
        for input in self.model.inputs.iter() {
            let lit = input.lit();
            match unblock.sat.lit_value(lit) {
                Some(true) => assumption.push(lit),
                Some(false) => assumption.push(!lit),
                None => (),
            }
        }
        let mut latchs = Cube::new();
        for latch in self.model.latchs.iter() {
            let lit = latch.lit();
            match unblock.sat.lit_value(lit) {
                Some(true) => latchs.push(lit),
                Some(false) => latchs.push(!lit),
                None => (),
            }
        }
        self.activity.sort_by_activity(&mut latchs, false);
        assumption.extend_from_slice(&latchs);
        let res: Cube = match self.lift.solver.solve(&assumption) {
            SatResult::Sat(_) => panic!(),
            SatResult::Unsat(conflict) => latchs.into_iter().filter(|l| conflict.has(*l)).collect(),
        };
        self.lift.solver.add_clause(&[!act]);
        self.statistic.minimal_predecessor_time += start.elapsed();
        res
    }
}
