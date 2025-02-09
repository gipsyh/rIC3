use super::Transys;
use crate::transys::unroll::TransysUnroll;
use giputils::hash::GHashMap;
use logic_form::{LitVec, Var};
use satif::Satif;
use satif_cadical::Solver;

impl Transys {
    pub fn simulations(&self) -> Vec<LitVec> {
        let mut uts = TransysUnroll::new(self);
        let depth = 5;
        uts.unroll_to(depth);
        let mut solver = Solver::new();
        self.load_init(&mut solver);
        for k in 0..=depth {
            uts.load_trans(&mut solver, k, true);
        }
        let mut res = vec![];
        let ninit: LitVec = uts.lits_next(&self.init, depth + 1);
        solver.add_clause(&!&ninit);
        while res.len() < 64 {
            if !solver.solve(&[]) {
                break;
            };
            let mut cube = LitVec::new();
            for l in self.latchs.iter() {
                let l = l.lit();
                let nl = uts.lit_next(l, depth + 1);
                if let Some(v) = solver.sat_value(nl) {
                    cube.push(l.not_if(!v));
                    solver.set_polarity(nl.var(), Some(!v))
                }
            }
            for r in res.iter().skip(1) {
                let its = cube.intersection(r);
                let nits: LitVec = uts.lits_next(&its, depth + 1);
                solver.add_clause(&!&nits);
            }
            let ncube: LitVec = uts.lits_next(&cube, depth + 1);
            solver.add_clause(&!&ncube);
            res.push(cube);
        }
        res
    }

    pub fn simulation_bv(&self, simulation: Vec<LitVec>) -> Option<GHashMap<Var, u64>> {
        let mut bv = GHashMap::new();
        for v in self.latchs.iter() {
            bv.insert(*v, 0);
        }
        for (i, s) in simulation.into_iter().enumerate() {
            if s.len() != self.latchs.len() {
                return None;
            }
            for l in s.iter() {
                let bv = bv.get_mut(&l.var()).unwrap();
                if l.polarity() {
                    *bv |= 1 << i;
                }
            }
        }
        Some(bv)
    }
}
