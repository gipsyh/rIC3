use crate::{
    config::PreprocessConfig,
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf, certify::Restore},
};
use giputils::{bitvec::BitVec, hash::GHashMap};
use log::{info, trace};
use logicrs::{Lit, LitVec, Var, VarLMap, satif::Satif};
use std::time::Instant;

pub struct Scorr {
    ts: Transys,
    rst: Restore,
    init_slv: DagCnfSolver,
    ind_slv: DagCnfSolver,
    cfg: PreprocessConfig,
}

impl Scorr {
    pub fn new(ts: Transys, cfg: &PreprocessConfig, rst: Restore) -> Self {
        let mut ind_slv = DagCnfSolver::new(&ts.rel);
        for c in ts.constraint.iter() {
            ind_slv.add_clause(&[*c]);
        }
        let mut init_slv = DagCnfSolver::new(&ts.rel);
        for c in ts.constraint.iter() {
            init_slv.add_clause(&[*c]);
        }
        ts.load_init(&mut init_slv);
        Self {
            ts,
            rst,
            ind_slv,
            init_slv,
            cfg: cfg.clone(),
        }
    }

    fn check_scorr(&mut self, x: Lit, y: Lit) -> bool {
        if self
            .init_slv
            .solve_with_restart_limit(&[], vec![LitVec::from([x, y]), LitVec::from([!x, !y])], 10)
            .is_none_or(|r| r)
        {
            return false;
        }
        let xn = self.ts.next(x);
        let yn = if y.var().is_constant() {
            y
        } else {
            self.ts.next(y)
        };
        self.ind_slv
            .solve_with_restart_limit(
                &[],
                vec![
                    LitVec::from([x, !y]),
                    LitVec::from([!x, y]),
                    LitVec::from([xn, yn]),
                    LitVec::from([!xn, !yn]),
                ],
                10,
            )
            .is_some_and(|r| !r)
    }

    pub fn scorr(mut self) -> (Transys, Restore) {
        let start = Instant::now();
        let init = self.ts.init_simulation(1);
        if init.bv_len() == 0 {
            return (self.ts, self.rst);
        }
        let mut rt = self.ts.rt_simulation(&init, 10);
        info!(
            "scorr: init simulation size: {}, rt simulation size: {}",
            init.bv_len(),
            rt.bv_len()
        );
        let mut latch: Vec<_> = self.ts.latch().filter(|v| !init[*v].is_empty()).collect();
        latch.sort();
        for i in 0..init.bv_len() {
            rt[Var::CONST].push(false);
            for &l in latch.iter() {
                rt[l].push(init[l].get(i));
            }
        }
        let mut cand: GHashMap<BitVec, LitVec> = GHashMap::new();
        cand.insert(rt[Var::CONST].clone(), LitVec::from([Lit::constant(false)]));
        for &v in latch.iter() {
            let l = v.lit();
            if let Some(c) = cand.get_mut(&rt[v]) {
                c.push(l);
            } else if let Some(c) = cand.get_mut(&rt.val(!l)) {
                c.push(!l);
            } else {
                cand.insert(rt[v].clone(), LitVec::from([l]));
            }
        }
        let mut scorr = VarLMap::new();
        // for eqc in cand.values() {
        //     if eqc.len() > 200 {
        //         dbg!(eqc.len());
        //     }
        // }
        'm: for x in latch {
            if let Some(n) = self.ts.init.get(&x)
                && !n.var().is_constant()
            {
                continue;
            }
            let (eqc, xl) = if let Some(eqc) = cand.get_mut(&rt[x]) {
                (eqc, x.lit())
            } else if let Some(eqc) = cand.get_mut(&rt.val(!x.lit())) {
                (eqc, !x.lit())
            } else {
                panic!();
            };
            for i in 0..eqc.len() {
                if i > (10000 / eqc.len()).max(1) {
                    break;
                }
                if start.elapsed().as_secs() > self.cfg.scorr_tl {
                    info!("scorr: timeout");
                    break 'm;
                }
                let y = eqc[i];
                if y.var() >= x {
                    break;
                }
                if self.check_scorr(xl, y) {
                    trace!("scorr: {xl} -> {y}");
                    scorr.insert_lit(xl, y);
                    eqc.retain(|l| l.var() != x);
                    break;
                }
            }
        }
        info!(
            "scorr: eliminates {} latchs out of {} in {:.2}s",
            scorr.len(),
            self.ts.latch.len(),
            start.elapsed().as_secs_f32()
        );
        // for (x, r) in scorr.clone().iter() {
        //     let mut xn = self.ts.next(x.lit());
        //     let mut rn = if r.var().is_constant() {
        //         *r
        //     } else {
        //         self.ts.next(*r)
        //     };
        //     if xn.var() == rn.var() {
        //         continue;
        //     }
        //     if xn.var() < rn.var() {
        //         (xn, rn) = (rn, xn);
        //     }
        //     trace!("scorr: {xn} -> {rn}");
        //     scorr.insert_lit(xn, rn);
        // }
        // let mut vars: Vec<Var> = scorr.keys().copied().collect();
        // vars.sort();
        // for v in vars {
        //     let r = scorr[&v];
        //     if let Some(rr) = scorr.map_lit(r) {
        //         if rr.var() != r.var() {
        //             scorr.insert_lit(v.lit(), rr);
        //         }
        //     }
        // }
        self.ts.replace(&scorr, &mut self.rst);
        self.ts.simplify(&mut self.rst);
        info!("scorr: simplified ts: {}", self.ts.statistic());
        (self.ts, self.rst)
    }
}
