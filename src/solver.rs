use super::{Frames, IC3};
use giputils::grc::Grc;
use logic_form::{Clause, Cube, Lit};
use satif::Satif;
use std::ops::Deref;
use transys::Transys;

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
                self.add_clause(&!cube.deref().deref().clone());
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

    pub fn add_clause(&mut self, clause: &Clause) {
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
        self.solvers[frame - 1].inductive(cube, strengthen)
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

    pub fn get_bad(&mut self) -> Option<(Cube, Cube)> {
        let solver = self.solvers.last_mut().unwrap();
        solver.finish_last();
        self.statistic.qbad_num += 1;
        let qbad_start = self.statistic.time.start();
        let res = solver.solver.solve(&[self.ts.bad]);
        solver.assumption = self.ts.bad.cube();
        self.statistic.qbad_avg_time += self.statistic.time.stop(qbad_start);
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
