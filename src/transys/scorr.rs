use std::time::Instant;

use crate::{
    config::Config,
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf},
};
use giputils::{bitvec::BitVec, hash::GHashMap};
use log::info;
use logicrs::{Lit, LitVec, Var, VarLMap, VarVMap, satif::Satif};

pub struct Scorr {
    ts: Transys,
    rst: VarVMap,
    init_slv: DagCnfSolver,
    ind_slv: DagCnfSolver,
}

impl Scorr {
    pub fn new(ts: Transys, _cfg: &Config, rst: VarVMap) -> Self {
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
        }
    }

    fn check_scorr(&mut self, x: Lit, y: Lit) -> bool {
        if self
            .init_slv
            .solve_with_constraint(&[], vec![LitVec::from([x, y]), LitVec::from([!x, !y])])
        {
            return false;
        }
        let xn = self.ts.next(x).unwrap();
        let yn = if y.var().is_constant() {
            y
        } else {
            self.ts.next(y).unwrap()
        };
        !self.ind_slv.solve_with_constraint(
            &[],
            vec![
                LitVec::from([x, !y]),
                LitVec::from([!x, y]),
                LitVec::from([xn, yn]),
                LitVec::from([!xn, !yn]),
            ],
        )
    }

    pub fn scorr(mut self) -> (Transys, VarVMap) {
        let start = Instant::now();
        let init = self.ts.init_simulation(1);
        let mut rt = self.ts.rt_simulation2(&init, 10);
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
        //     if eqc.len() > 1 {
        //         // dbg!(eqc.len());
        //     }
        // }
        for x in latch {
            // println!("scorr: check {x}");
            let (eqc, xl) = if let Some(eqc) = cand.get_mut(&rt[x]) {
                (eqc, x.lit())
            } else if let Some(eqc) = cand.get_mut(&rt.val(!x.lit())) {
                (eqc, !x.lit())
            } else {
                panic!();
            };
            if eqc.len() > 100 {
                continue;
            }
            for i in 0..eqc.len() {
                let y = eqc[i];
                if y.var() >= x {
                    break;
                }
                // println!("check scorr: {x}, {y}");
                if self.check_scorr(xl, y) {
                    // dbg!(xl, y);
                    scorr.insert_lit(xl, y);
                    eqc.retain(|l| l.var() != x);
                    break;
                }
            }
        }
        // dbg!(self.ts.statistic());
        info!(
            "scorr: eliminates {} latchs out of {} in {:.2}s",
            scorr.len(),
            self.ts.latch.len(),
            start.elapsed().as_secs_f32()
        );
        let replace = scorr.clone();
        // for (x, r) in scorr.iter() {
        //     let mut xn = self.ts.next(x.lit()).unwrap();
        //     let mut rn = if r.var().is_constant() {
        //         *r
        //     } else {
        //         self.ts.next(*r).unwrap()
        //     };
        //     if xn.var() == rn.var() {
        //         continue;
        //     }
        //     if xn.var() < rn.var() {
        //         (xn, rn) = (rn, xn);
        //     }
        //     replace.insert_lit(xn, rn);
        // }
        self.ts.latch.retain(|l| !scorr.contains_key(l));
        self.ts.init.retain(|l, _| !scorr.contains_key(l));
        self.ts.next.retain(|l, _| !scorr.contains_key(l));
        self.ts.replace(&replace, &mut self.rst);
        self.ts.simplify(&mut self.rst);
        info!("scorr: simplified ts: {}", self.ts.statistic());
        (self.ts, self.rst)
    }
}
