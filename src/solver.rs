use super::{Frames, IC3};
use logic_form::{Clause, Cube, Lit};
use satif::Satif;
use std::{ops::Deref, rc::Rc};
use transys::Transys;

pub type SatSolver = satif_minisat::Solver;

pub struct Ic3Solver {
    solver: Box<SatSolver>,
    ts: Rc<Transys>,
    num_act: usize,
    frame: usize,
}

impl Ic3Solver {
    pub fn new(ts: &Rc<Transys>, frame: usize) -> Self {
        let ts = ts.clone();
        let mut solver = Box::new(SatSolver::new());
        ts.load_trans(solver.as_mut(), true);
        Self {
            solver,
            ts,
            frame,
            num_act: 0,
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
                self.add_clause(&!cube.deref().deref().clone());
            }
        }
    }

    pub fn add_clause(&mut self, clause: &Clause) {
        self.solver.add_clause(clause);
    }

    #[allow(unused)]
    pub fn solve(&mut self, assumptions: &[Lit]) -> bool {
        self.solver.solve(assumptions)
    }

    fn inductive(&mut self, cube: &Cube, strengthen: bool) -> BlockResult {
        let mut assumption = self.ts.cube_next(cube);
        let res = if strengthen {
            let act = self.solver.new_var().into();
            assumption.push(act);
            let mut tmp_cls = !cube;
            tmp_cls.push(!act);
            self.solver.add_clause(&tmp_cls);
            let res = self.solver.solve(&assumption);
            let act = !assumption.pop().unwrap();
            if res {
                BlockResult::No(BlockResultNo {
                    solver: self.solver.as_mut(),
                    assumption,
                    act: Some(act),
                })
            } else {
                BlockResult::Yes(BlockResultYes {
                    solver: self.solver.as_mut(),
                    cube: cube.clone(),
                    assumption,
                    act: Some(act),
                })
            }
        } else {
            if self.solver.solve(&assumption) {
                BlockResult::No(BlockResultNo {
                    solver: self.solver.as_mut(),
                    assumption,
                    act: None,
                })
            } else {
                BlockResult::Yes(BlockResultYes {
                    solver: self.solver.as_mut(),
                    cube: cube.clone(),
                    assumption,
                    act: None,
                })
            }
        };
        res
    }
}

impl IC3 {
    pub fn blocked(&mut self, frame: usize, cube: &Cube, strengthen: bool) -> BlockResult {
        assert!(!self.ts.cube_subsume_init(cube));
        let solver = &mut self.solvers[frame - 1];
        solver.num_act += 1;
        if solver.num_act > 1000 {
            solver.reset(&self.frame);
        }
        self.solvers[frame - 1].inductive(cube, strengthen)
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

    pub fn get_bad(&mut self) -> Option<(Cube, Cube)> {
        let solver = self.solvers.last_mut().unwrap();
        let res = if solver.solver.solve(&[self.ts.bad]) {
            Some(BlockResultNo {
                assumption: Cube::from([self.ts.bad]),
                solver: solver.solver.as_mut(),
                act: None,
            })
        } else {
            None
        };
        res.map(|res| self.get_predecessor(res))
    }
}

pub enum BlockResult {
    Yes(BlockResultYes),
    No(BlockResultNo),
}

pub struct BlockResultYes {
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
    solver: *mut SatSolver,
    assumption: Cube,
    act: Option<Lit>,
}

impl BlockResultNo {
    #[inline]
    pub fn lit_value(&self, lit: Lit) -> Option<bool> {
        let solver = unsafe { &mut *self.solver };
        solver.sat_value(lit)
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

impl IC3 {
    pub fn inductive_core(&mut self, block: BlockResultYes) -> Cube {
        let mut ans = Cube::new();
        let solver = unsafe { &mut *block.solver };
        for i in 0..block.cube.len() {
            if solver.unsat_has(block.assumption[i]) {
                ans.push(block.cube[i]);
            }
        }
        if self.ts.cube_subsume_init(&ans) {
            ans = Cube::new();
            let new = *block
                .cube
                .iter()
                .find(|l| self.ts.init_map[l.var()].is_some_and(|i| i != l.polarity()))
                .unwrap();
            for i in 0..block.cube.len() {
                if solver.unsat_has(block.assumption[i]) || block.cube[i] == new {
                    ans.push(block.cube[i]);
                }
            }
            assert!(!self.ts.cube_subsume_init(&ans));
        }
        ans
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
    pub fn get_predecessor(&mut self, unblock: BlockResultNo) -> (Cube, Cube) {
        let solver = unsafe { &mut *unblock.solver };
        self.lift.num_act += 1;
        if self.lift.num_act > 1000 {
            self.lift = Lift::new(&self.ts)
        }
        let act: Lit = self.lift.solver.new_var().into();
        let mut assumption = Cube::from([act]);
        let mut cls = unblock.assumption.clone();
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
