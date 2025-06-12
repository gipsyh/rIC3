use crate::{
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf},
};
use giputils::hash::GHashMap;
use log::info;
use logic_form::{LitVec, Var, VarLMap, VarVMap, simulate::DagCnfSimulation};
use satif::Satif;
use std::time::Instant;

pub struct FrTs {
    ts: Transys,
    sim: DagCnfSimulation,
    map: VarLMap,
    solver: DagCnfSolver,
    rseed: u64,
    rst: VarVMap,
}

impl FrTs {
    pub fn new(ts: Transys, rseed: u64, rst: VarVMap) -> Self {
        let sim = DagCnfSimulation::new(1000, &ts.rel);
        let solver = DagCnfSolver::new(&ts.rel, rseed);
        Self {
            ts,
            sim,
            map: VarLMap::new(),
            solver,
            rseed,
            rst,
        }
    }

    fn setup_candicate(&mut self) {
        let mut simval: GHashMap<_, Vec<_>> = GHashMap::new();
        self.map.clear();
        for v in self.ts.rel.var_iter() {
            let lv = v.lit();
            let slv = self.sim.val(lv);
            let snlv = self.sim.val(!lv);
            if let Some(e) = simval.get_mut(&slv) {
                e.push(lv);
                self.map.insert_lit(lv, e[0]);
            } else if let Some(e) = simval.get_mut(&snlv) {
                e.push(!lv);
                self.map.insert_lit(!lv, e[0]);
            } else {
                simval.insert(slv, vec![lv]);
            }
        }
    }

    pub fn restart(&mut self) {
        self.solver = DagCnfSolver::new(&self.ts.rel, self.rseed);
    }

    pub fn fr(mut self) -> (Transys, VarVMap) {
        let start = Instant::now();
        let before = self.ts.max_var();
        const NUM_RESTART: usize = 10000;
        self.setup_candicate();
        let mut replace = VarLMap::new();
        // let mut num_timeout = 0;
        let mut num_replace = 0;
        let mut v = Var(1);
        let mut cadical = cadical::Solver::new();
        // let mut solver = DagCnfSolver::new(&self.ts.rel, self.rseed);
        for cls in self.ts.rel.clause() {
            cadical.add_clause(cls);
        }
        while v <= self.ts.max_var() {
            let Some(m) = self.map.map(v) else {
                v += 1;
                continue;
            };
            let lv = v.lit();
            // dbg!(m, v);
            let res = cadical.solve(&[!m, lv]) || cadical.solve(&[m, !lv]);
            // let res2 = solver.solve(&[!m, lv]) || cadical.solve(&[m, !lv]);
            match self.solver.solve_with_restart_limit(
                &[],
                vec![LitVec::from([m, lv]), LitVec::from([!m, !lv])],
                15,
            ) {
                Some(true) => {
                    // dbg!(res);
                    // dbg!(res2);
                    assert!(res);
                    // assert!(res2);
                    // self.sim.add(self.solver.sat_bitvet());
                    // num_cex += 1;
                    // if num_cex == 64 {
                    //     num_cex = 0;
                    //     self.sim.simulate(&self.ts.rel);
                    //     self.setup_candicate();
                    // }
                }
                Some(false) => {
                    assert!(!res);
                    // assert!(!res2);
                    // dbg!("can replace");
                    replace.insert_lit(lv, m);
                    num_replace += 1;
                    if num_replace >= NUM_RESTART {
                        num_replace = 0;
                        // num_timeout = 0;
                        // dbg!("restart");
                        // self.ts.replace(&replace, &mut self.rst);
                        // self.restart();
                    }
                }
                None => {
                    // num_timeout += 1;
                    // dbg!(num_timeout);
                }
            }
            v += 1;
        }
        self.ts.replace(&replace, &mut self.rst);
        self.ts.coi_refine(&mut self.rst);
        self.ts.rearrange(&mut self.rst);
        info!(
            "frts eliminates {} out of {} vars in {:.2}s.",
            *before - *self.ts.max_var(),
            *before,
            start.elapsed().as_secs_f32()
        );
        (self.ts, self.rst)
    }
}
