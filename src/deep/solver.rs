use super::Deep;
use crate::transys::Transys;
use logic_form::{Cube, Lit};
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
            Some(self.get_predecessor(&self.ts.bad.clone()))
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

// impl IC3 {
//     pub fn inductive_core(&mut self, block: BlockResultYes) -> Cube {
//         let mut ans = Cube::new();
//         let solver = unsafe { &mut *block.solver };
//         for i in 0..block.cube.len() {
//             if solver.unsat_has(block.assumption[i]) {
//                 ans.push(block.cube[i]);
//             }
//         }
//         if self.ts.cube_subsume_init(&ans) {
//             ans = Cube::new();
//             let new = *block
//                 .cube
//                 .iter()
//                 .find(|l| self.ts.init_map[l.var()].is_some_and(|i| i != l.polarity()))
//                 .unwrap();
//             for i in 0..block.cube.len() {
//                 if solver.unsat_has(block.assumption[i]) || block.cube[i] == new {
//                     ans.push(block.cube[i]);
//                 }
//             }
//             assert!(!self.ts.cube_subsume_init(&ans));
//         }
//         ans
//     }
// }

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

impl Deep {
    pub fn get_predecessor(&mut self, assump: &Cube) -> (Cube, Cube) {
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
        // self.activity.sort_by_activity(&mut latchs, false);
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
