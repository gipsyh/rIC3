use super::Deep;
use crate::transys::Transys;
use logic_form::{Cube, Lit};
use rand::seq::SliceRandom;
use satif::Satif;
use std::ops::{Deref, DerefMut};

pub type SatSolver = satif_minisat::Solver;

pub struct DeepSolver {
    solver: Box<SatSolver>,
    num_act: usize,
}

impl DeepSolver {
    pub fn new(ts: &Transys) -> Self {
        let mut solver = Box::new(SatSolver::new());
        ts.load_trans(solver.as_mut(), true);
        Self { solver, num_act: 0 }
    }
}

impl Deref for DeepSolver {
    type Target = SatSolver;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.solver
    }
}

impl DerefMut for DeepSolver {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.solver
    }
}

impl Deep {
    pub fn get_bad(&mut self) -> Option<(Cube, Cube)> {
        if self.solver.solve(&self.ts.bad) {
            Some(self.get_predecessor(&self.ts.bad.clone(), true))
        } else {
            None
        }
    }
}

// impl IC3 {
//     pub fn get_bad(&mut self) -> Option<(Cube, Cube)> {
//         let solver = self.solvers.last_mut().unwrap();
//         let res = if solver.solver.solve(&self.ts.bad) {
//             Some(BlockResultNo {
//                 assumption: self.ts.bad.clone(),
//                 solver: solver.solver.as_mut(),
//                 act: None,
//             })
//         } else {
//             None
//         };
//         res.map(|res| self.get_predecessor(res))
//     }
// }

// pub enum BlockResult {
//     Yes(BlockResultYes),
//     No(BlockResultNo),
// }

// pub struct BlockResultYes {
//     solver: *mut SatSolver,
//     cube: Cube,
//     assumption: Cube,
//     act: Option<Lit>,
// }

// impl Drop for BlockResultYes {
//     fn drop(&mut self) {
//         if let Some(act) = self.act {
//             let solver = unsafe { &mut *self.solver };
//             solver.add_clause(&[act]);
//         }
//     }
// }

// pub struct BlockResultNo {
//     solver: *mut SatSolver,
//     assumption: Cube,
//     act: Option<Lit>,
// }

// impl BlockResultNo {
//     #[inline]
//     pub fn lit_value(&self, lit: Lit) -> Option<bool> {
//         let solver = unsafe { &mut *self.solver };
//         solver.sat_value(lit)
//     }
// }

// impl Drop for BlockResultNo {
//     fn drop(&mut self) {
//         if let Some(act) = self.act {
//             let solver = unsafe { &mut *self.solver };
//             solver.add_clause(&[act]);
//         }
//     }
// }

impl Deep {
    pub fn unsat_core(&mut self, cube: &Cube) -> Cube {
        let next = self.ts.cube_next(&cube);
        let mut ans = Cube::new();
        for i in 0..cube.len() {
            if self.solver.unsat_has(next[i]) {
                ans.push(cube[i]);
            }
        }
        if self.ts.cube_subsume_init(&ans) {
            ans = Cube::new();
            let new = *cube
                .iter()
                .find(|l| self.ts.init_map[l.var()].is_some_and(|i| i != l.polarity()))
                .unwrap();
            for i in 0..cube.len() {
                if self.solver.unsat_has(next[i]) || cube[i] == new {
                    ans.push(cube[i]);
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

    fn minimal_predecessor(
        &mut self,
        inputs: &[Lit],
        latchs: &[Lit],
        constrain: Lit,
    ) -> Option<Cube> {
        let mut assump = Cube::from_iter(inputs.iter().chain(latchs.iter()).copied());
        assump.push(constrain);
        if self.solver.solve(&assump) {
            return None;
        }
        Some(
            latchs
                .iter()
                .filter(|l| self.solver.unsat_has(**l))
                .copied()
                .collect(),
        )
    }
}

impl Deep {
    pub fn get_predecessor(&mut self, assump: &Cube, strengthen: bool) -> (Cube, Cube) {
        self.lift.num_act += 1;
        if self.lift.num_act > 1000 {
            self.lift = Lift::new(&self.ts)
        }
        let act: Lit = self.lift.solver.new_var().into();
        let mut assumption = Cube::from([act]);
        let mut cls = assump.clone();
        cls.extend_from_slice(&self.ts.constraints);
        cls.push(act);
        let cls = !cls;
        let mut inputs = Cube::new();
        self.lift.solver.add_clause(&cls);
        for input in self.ts.inputs.iter() {
            let lit = input.lit();
            if let Some(v) = self.solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        assumption.extend_from_slice(&inputs);
        let mut latchs = Cube::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            match self.solver.sat_value(lit) {
                Some(true) => latchs.push(lit),
                Some(false) => latchs.push(!lit),
                None => (),
            }
        }
        for _ in 0.. {
            if latchs.is_empty() {
                break;
            }
            latchs.shuffle(&mut self.rng);
            let olen = latchs.len();
            latchs = self
                .lift
                .minimal_predecessor(&inputs, &latchs, act)
                .unwrap();
            if latchs.len() == olen || !strengthen {
                break;
            }
        }
        self.lift.solver.add_clause(&[!act]);
        (latchs, inputs)
    }
}
