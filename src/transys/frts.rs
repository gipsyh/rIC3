use crate::{
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf},
};
use giputils::hash::GHashMap;
use log::info;
use logicrs::{Lit, LitVec, Var, VarLMap, VarMap, VarVMap, simulate::DagCnfSimulation};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::time::Instant;

#[allow(unused)]
pub struct FrTs {
    ts: Transys,
    candidate: VarMap<Vec<Lit>>,
    map: VarLMap,
    eqc: VarVMap,
    solver: DagCnfSolver,
    rseed: u64,
    rng: StdRng,
    rst: VarVMap,
}

impl FrTs {
    pub fn new(mut ts: Transys, rseed: u64, mut rst: VarVMap) -> Self {
        ts.topsort(&mut rst);
        let sim = DagCnfSimulation::new(1000, &ts.rel);
        let solver = DagCnfSolver::new(&ts.rel, rseed);
        let mut map = VarLMap::new();
        let mut eqc = VarVMap::new();
        let mut simval: GHashMap<_, Vec<_>> = GHashMap::new();
        let mut candidate: VarMap<Vec<Lit>> = VarMap::new_with(ts.max_var());
        for v in ts.rel.var_iter() {
            let lv = v.lit();
            let slv = sim.val(lv);
            let snlv = sim.val(!lv);
            if let Some(e) = simval.get_mut(&slv) {
                e.push(lv);
                map.insert_lit(lv, e[0]);
                eqc.insert(lv.var(), e[0].var());
                candidate[e[0].var()].push(lv);
            } else if let Some(e) = simval.get_mut(&snlv) {
                e.push(!lv);
                map.insert_lit(!lv, e[0]);
                eqc.insert(lv.var(), e[0].var());
                candidate[e[0].var()].push(!lv);
            } else {
                simval.insert(slv, vec![lv]);
                candidate[lv.var()].push(lv);
            }
        }
        let rng = StdRng::seed_from_u64(rseed);
        Self {
            ts,
            candidate,
            map,
            eqc,
            solver,
            rseed,
            rst,
            rng,
        }
    }

    pub fn restart(&mut self) {
        self.solver = DagCnfSolver::new(&self.ts.rel, self.rng.random());
    }

    pub fn fr(mut self) -> (Transys, VarVMap) {
        let start = Instant::now();
        let before = self.ts.max_var();
        const NUM_RESTART: usize = 200;
        let mut replace = VarLMap::new();
        let mut v = Var(1);
        while v <= self.ts.max_var() {
            let Some(m) = self.map.map(v) else {
                v += 1;
                continue;
            };
            let lv = v.lit();
            // dbg!(m, v);
            match self.solver.solve_with_restart_limit(
                &[],
                vec![LitVec::from([m, lv]), LitVec::from([!m, !lv])],
                15,
            ) {
                Some(true) => {
                    // let eqc = self.eqc[v];
                    // let rlv = *self.candidate[eqc].iter().find(|l| l.var() == v).unwrap();
                    // let rlvs = self.solver.sat_value(rlv).unwrap();
                    // if let Some(newm) = self.candidate[eqc]
                    //     .iter()
                    //     .filter(|l| {
                    //         !replace.contains_key(&l.var()) && l.var() < v && l.var() > m.var()
                    //     })
                    //     .find(|&l| self.solver.sat_value(*l).is_some_and(|x| x == rlvs))
                    // {
                    //     self.map.insert_lit(rlv, *newm);
                    //     continue;
                    // }
                }
                Some(false) => {
                    // dbg!("can replace");
                    replace.insert_lit(lv, m);
                    if replace.len() % NUM_RESTART == 0 {
                        self.ts.replace(&replace, &mut self.rst);
                        self.solver = DagCnfSolver::new(&self.ts.rel, 5);
                    }
                }
                None => {
                    // dbg!("to");
                }
            }
            v += 1;
        }
        self.ts.replace(&replace, &mut self.rst);
        self.ts.coi_refine(&mut self.rst);
        self.ts.rearrange(&mut self.rst);
        info!(
            "frts eliminates {} out of {} vars in {:.2}s",
            *before - *self.ts.max_var(),
            *before,
            start.elapsed().as_secs_f32()
        );
        self.ts.simplify(&mut self.rst);
        (self.ts, self.rst)
    }
}
