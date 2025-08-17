use crate::{
    config::Config,
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf},
};
use giputils::hash::GHashMap;
use log::{debug, info};
use logicrs::{Lit, LitVec, Var, VarLMap, VarMap, VarVMap, simplify::DagCnfSimplify};
use rand::{SeedableRng, rngs::StdRng};
use std::time::Instant;

#[allow(unused)]
pub struct FrTs {
    cfg: Config,
    ts: Transys,
    candidate: VarMap<Vec<Lit>>,
    map: VarLMap,
    eqc: VarVMap,
    solver: DagCnfSolver,
    rng: StdRng,
    rst: VarVMap,
}

impl FrTs {
    pub fn new(mut ts: Transys, cfg: &Config, mut rst: VarVMap) -> Self {
        ts.topsort(&mut rst);
        let sim = ts.rel.simulation(1000);
        let solver = DagCnfSolver::new(&ts.rel);
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
        let rng = StdRng::seed_from_u64(cfg.rseed);
        Self {
            ts,
            cfg: cfg.clone(),
            candidate,
            map,
            eqc,
            solver,
            rst,
            rng,
        }
    }

    pub fn fr(mut self) -> (Transys, VarVMap) {
        let start = Instant::now();
        let before = self.ts.max_var();
        let mut replace = VarLMap::new();
        let mut v = Var(1);
        while v <= self.ts.max_var() {
            if start.elapsed().as_secs() > self.cfg.preproc.frts_tl {
                info!("frts: timeout");
                break;
            }
            if self.ts.rel.is_leaf(v) {
                v += 1;
                continue;
            }
            let Some(m) = self.map.map(v) else {
                v += 1;
                continue;
            };
            let lv = v.lit();
            debug!("frts: checking var {m} with lit {v}");
            match self.solver.solve_with_restart_limit(
                &[],
                vec![LitVec::from([m, lv]), LitVec::from([!m, !lv])],
                1,
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
                    debug!("frts: replace {v} with {m}");
                    replace.insert_lit(lv, m);
                    self.solver.add_eq(lv, m);
                    if replace.len() % 5000 == 0 {
                        self.ts.replace(&replace, &mut self.rst);
                        self.ts.coi_refine(&mut self.rst);
                        let mut simp = DagCnfSimplify::new(&self.ts.rel);
                        for &v in self.ts.frozens().iter() {
                            simp.froze(v);
                        }
                        simp.const_simplify();
                        simp.bve_simplify();
                        self.ts.rel = simp.finalize();
                        self.solver = DagCnfSolver::new(&self.ts.rel);
                        info!("frts ts simplified to: {}", self.ts.statistic());
                    }
                }
                None => {
                    debug!("frts: checking {v} with {m} timeout");
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
