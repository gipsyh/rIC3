use super::Transys;
use logic_form::{Lit, LitMap, LitVec, Var};
use satif::Satif;

#[derive(Debug)]
pub struct TransysUnroll {
    pub ts: Transys,
    pub num_unroll: usize,
    pub max_var: Var,
    next_map: LitMap<Vec<Lit>>,
    simple_path: Option<Vec<Vec<LitVec>>>,
}

impl TransysUnroll {
    pub fn new(ts: &Transys) -> Self {
        let mut next_map: LitMap<Vec<_>> = LitMap::new();
        next_map.reserve(ts.max_var());
        let false_lit = Lit::constant(false);
        next_map[false_lit].push(false_lit);
        next_map[!false_lit].push(!false_lit);
        for v in Var::new(0)..=ts.max_var() {
            let l = v.lit();
            if next_map[l].is_empty() {
                next_map[l].push(l);
                next_map[!l].push(!l);
            }
        }
        for l in ts.latchs.iter() {
            let l = l.lit();
            let next = ts.lit_next(l);
            next_map[l].push(next);
            next_map[!l].push(!next);
        }
        Self {
            ts: ts.clone(),
            num_unroll: 0,
            max_var: ts.max_var(),
            next_map,
            simple_path: None,
        }
    }

    pub fn new_with_simple_path(ts: &Transys) -> Self {
        let mut res = Self::new(ts);
        res.simple_path = Some(Vec::new());
        res
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.max_var += 1;
        self.max_var
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit, num: usize) -> Lit {
        self.next_map[lit][num]
    }

    #[inline]
    #[allow(unused)]
    pub fn lits_next<R: FromIterator<Lit> + AsRef<[Lit]>>(&self, lits: &R, num: usize) -> R {
        lits.as_ref()
            .iter()
            .map(|l| self.lit_next(*l, num))
            .collect()
    }

    fn single_simple_path(&mut self, i: usize, j: usize) {
        let mut ors = LitVec::new();
        for l in self.ts.latchs.iter() {
            let l = l.lit();
            let li = self.lit_next(l, i);
            let lj = self.lit_next(l, j);
            self.max_var += 1;
            let n = self.max_var.lit();
            let rel = vec![
                LitVec::from([!li, lj, n]),
                LitVec::from([li, !lj, n]),
                LitVec::from([li, lj, !n]),
                LitVec::from([!li, !lj, !n]),
            ];
            self.simple_path.as_mut().unwrap()[self.num_unroll - 1].extend(rel.into_iter());
            ors.push(n);
        }
        self.simple_path.as_mut().unwrap()[self.num_unroll - 1].push(ors);
    }

    fn simple_path(&mut self) {
        let simple_path = self.simple_path.as_mut().unwrap();
        assert!(simple_path.len() == self.num_unroll - 1);
        simple_path.push(Vec::new());
        for i in 0..self.num_unroll {
            self.single_simple_path(i, self.num_unroll);
        }
    }

    pub fn unroll(&mut self) {
        let false_lit = Lit::constant(false);
        self.next_map[false_lit].push(false_lit);
        self.next_map[!false_lit].push(!false_lit);
        for v in Var::CONST..=self.ts.max_var() {
            let l = v.lit();
            if self.next_map[l].len() == self.num_unroll + 1 {
                self.max_var += 1;
                let new = self.max_var.lit();
                self.next_map[l].push(new);
                self.next_map[!l].push(!new);
            }
            assert!(self.next_map[l].len() == self.num_unroll + 2);
        }
        for l in self.ts.latchs.iter() {
            let l = l.lit();
            let next = self.lit_next(self.ts.lit_next(l), self.num_unroll + 1);
            self.next_map[l].push(next);
            self.next_map[!l].push(!next);
        }
        self.num_unroll += 1;
        if self.simple_path.is_some() {
            self.simple_path();
        }
    }

    pub fn unroll_to(&mut self, k: usize) {
        while self.num_unroll < k {
            self.unroll()
        }
    }

    pub fn load_trans<S: Satif + ?Sized>(&self, satif: &mut S, u: usize, constraint: bool) {
        satif.new_var_to(self.max_var);
        for c in self.ts.rel.iter() {
            let c: Vec<Lit> = c.iter().map(|l| self.lit_next(*l, u)).collect();
            satif.add_clause(&c);
        }
        if constraint {
            for c in self.ts.constraints.iter() {
                let c = self.lit_next(*c, u);
                satif.add_clause(&[c]);
            }
        }
        if let Some(simple_path) = self.simple_path.as_ref() {
            if !simple_path.is_empty() {
                for c in simple_path[u - 1].iter() {
                    satif.add_clause(c);
                }
            }
        }
    }

    pub fn compile(&self) -> Transys {
        todo!()
        // let mut inputs = Vec::new();
        // let mut constraints = LitVec::new();
        // let mut trans = Vec::new();
        // for u in 0..=self.num_unroll {
        //     for i in self.ts.inputs.iter() {
        //         inputs.push(self.lit_next(i.lit(), u).var());
        //     }
        //     for c in self.ts.constraints.iter() {
        //         let c = self.lit_next(*c, u);
        //         constraints.push(c);
        //     }
        //     for c in self.ts.trans.iter() {
        //         let c: LitVec = self.lits_next(c, u);
        //         trans.push(c);
        //     }
        // }
        // let mut next_map = self.ts.next_map.clone();
        // let mut prev_map = self.ts.prev_map.clone();
        // for l in self.ts.latchs.iter() {
        //     let l = l.lit();
        //     let n = self.lit_next(l, self.num_unroll);
        //     next_map[l] = n;
        //     prev_map[n] = l;
        //     next_map[!l] = !n;
        //     prev_map[!n] = !l;
        // }
        // let mut dependence = self.ts.dependence.clone();
        // dependence.reserve(self.max_var);
        // for u in 1..=self.num_unroll {
        //     for i in 0..self.ts.num_var() {
        //         let v = Var::new(i);
        //         let n = self.lit_next(v.lit(), u).var();
        //         if dependence[n].is_empty() {
        //             dependence[n] = dependence[v]
        //                 .iter()
        //                 .map(|l| self.lit_next(l.lit(), u).var())
        //                 .collect()
        //         }
        //     }
        // }
        // Transys {
        //     inputs,
        //     latchs: self.ts.latchs.clone(),
        //     init: self.ts.init.clone(),
        //     bad: self.lit_next(self.ts.bad, 1),
        //     init_map: self.ts.init_map.clone(),
        //     constraints,
        //     trans,
        //     max_var: self.max_var,
        //     prev_map,
        //     next_map,
        //     dependence,
        //     max_latch: self.ts.max_latch,
        //     is_latch: self.ts.is_latch.clone(),
        //     restore: GHashMap::new(),
        // }
    }

    pub fn interal_signals(&self) -> Transys {
        // let mut trans = self.ts.trans.clone();
        // for c in self.ts.trans.iter() {
        //     trans.push(self.lits_next(c, 1));
        // }
        // let mut dependence = self.ts.dependence.clone();
        // dependence.reserve(self.max_var);
        // let mut next_map = self.ts.next_map.clone();
        // let mut prev_map = self.ts.prev_map.clone();
        // let mut is_latch = self.ts.is_latch.clone();
        // next_map.reserve(self.max_var);
        // prev_map.reserve(self.max_var);
        // is_latch.reserve(self.max_var);
        // for v in Var::new(1)..=self.ts.max_var {
        //     let l = v.lit();
        //     let n = self.lit_next(l, 1);
        //     next_map[l] = n;
        //     prev_map[n] = l;
        //     next_map[!l] = !n;
        //     prev_map[!n] = !l;
        //     if dependence[n].is_empty() {
        //         dependence[n] = dependence[l]
        //             .iter()
        //             .map(|l| self.lit_next(l.lit(), 1).var())
        //             .collect()
        //     }
        // }
        // let mut keep: GHashSet<Var> = GHashSet::from_iter(self.ts.inputs.iter().cloned());
        // for i in 0..self.ts.num_var() {
        //     let v = Var::new(i);
        //     if dependence[v].iter().any(|d| keep.contains(d)) {
        //         keep.insert(v);
        //     }
        // }
        // for l in self.ts.latchs.iter() {
        //     keep.insert(self.ts.var_next(*l));
        // }
        // if !self.ts.is_latch(self.ts.bad.var()) {
        //     keep.insert(self.ts.bad.var());
        // }
        // let mut latchs = Vec::new();
        // for v in Var::new(1)..=self.ts.max_var() {
        //     if !keep.contains(&v) {
        //         latchs.push(v);
        //         is_latch[v] = true;
        //     }
        // }
        // let max_latch = *latchs.last().unwrap_or(&Var::new(0));
        // let mut init_map = self.ts.init_map.clone();
        // init_map.reserve(max_latch);
        // let mut init = self.ts.init.clone();
        // let mut solver = satif_minisat::Solver::new();
        // solver.new_var_to(self.max_var);
        // for cls in trans.iter() {
        //     solver.add_clause(cls);
        // }
        // for c in self.ts.constraints.iter() {
        //     solver.add_clause(&[*c]);
        // }
        // let implies: GHashSet<Lit> = GHashSet::from_iter(solver.implies(&init));
        // for l in latchs.iter() {
        //     let l = l.lit();
        //     if implies.contains(&l) {
        //         init.push(l);
        //         init_map[l] = Some(true);
        //     } else if implies.contains(&!l) {
        //         init.push(!l);
        //         init_map[l] = Some(false);
        //     }
        // }
        // Transys {
        //     inputs: self.ts.inputs.clone(),
        //     latchs,
        //     init,
        //     bad: self.ts.bad,
        //     init_map,
        //     constraints: self.ts.constraints.clone(),
        //     trans,
        //     max_var: self.max_var,
        //     next_map,
        //     prev_map,
        //     dependence,
        //     max_latch,
        //     is_latch,
        //     restore: self.ts.restore.clone(),
        // }
        todo!()
    }
}
