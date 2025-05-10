use super::{Transys, TransysIf};
use giputils::hash::GHashMap;
use logic_form::{Lit, LitMap, LitVec, LitVvec, Var};
use satif::Satif;

#[derive(Debug)]
pub struct TransysUnroll<T: TransysIf> {
    pub ts: T,
    pub num_unroll: usize,
    pub max_var: Var,
    next_map: LitMap<Vec<Lit>>,
    simple_path: Option<Vec<Vec<LitVec>>>,
}

impl<T: TransysIf> TransysUnroll<T> {
    pub fn new(ts: &T) -> Self
    where
        T: Clone,
    {
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
        for l in ts.latch() {
            let l = l.lit();
            let next = ts.next(l);
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

    pub fn new_with_simple_path(ts: &T) -> Self
    where
        T: Clone,
    {
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
    pub fn var_next(&self, var: Var, num: usize) -> Var {
        self.next_map[var.lit()][num].var()
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
        for l in self.ts.latch() {
            let l = l.lit();
            let li = self.lit_next(l, i);
            let lj = self.lit_next(l, j);
            self.max_var += 1;
            let n = self.max_var.lit();
            let rel = LitVvec::cnf_xor(n, li, lj);
            self.simple_path.as_mut().unwrap()[self.num_unroll - 1].extend(rel);
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
        for l in self.ts.latch() {
            let l = l.lit();
            let next = self.lit_next(self.lit_next(l, 1), self.num_unroll + 1);
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
        for c in self.ts.trans() {
            let c: Vec<Lit> = c.iter().map(|l| self.lit_next(*l, u)).collect();
            satif.add_clause(&c);
        }
        if constraint {
            for c in self.ts.constraint() {
                let c = self.lit_next(c, u);
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
}
impl TransysUnroll<Transys> {
    pub fn compile(&self) -> Transys {
        let mut input = Vec::new();
        let mut constraint = LitVec::new();
        let mut rel = self.ts.rel.clone();
        for u in 0..=self.num_unroll {
            for i in self.ts.input.iter() {
                input.push(self.lit_next(i.lit(), u).var());
            }
            for c in self.ts.constraint.iter() {
                let c = self.lit_next(*c, u);
                constraint.push(c);
            }
            for (v, cls) in self.ts.rel.iter() {
                let v = self.var_next(v, u);
                if v <= rel.max_var() && rel.has_rel(v) {
                    continue;
                }
                let cls: Vec<_> = cls.iter().map(|c| self.lits_next(c, u)).collect();
                rel.add_rel(v, &cls);
            }
        }
        let next = self
            .ts
            .next
            .iter()
            .map(|(v, n)| (*v, self.lit_next(*n, self.num_unroll)))
            .collect();
        let bad = self.lit_next(self.ts.bad, self.num_unroll);
        Transys {
            input,
            latch: self.ts.latch.clone(),
            next,
            init: self.ts.init.clone(),
            bad,
            constraint,
            rel,
            rst: self.ts.rst.clone(),
        }
    }

    pub fn interal_signals(&self) -> Transys {
        assert!(self.num_unroll == 1);
        let keep = self.ts.rel.fanouts(self.ts.input());
        let mut rel = self.ts.rel.clone();
        for (v, cls) in self.ts.rel.iter() {
            if keep.contains(&v) {
                continue;
            }
            let v = self.var_next(v, 1);
            if v <= rel.max_var() && rel.has_rel(v) {
                continue;
            }
            let cls: Vec<_> = cls.iter().map(|c| self.lits_next(c, 1)).collect();
            rel.add_rel(v, &cls);
        }
        let mut latch = Vec::new();
        let mut next = GHashMap::new();
        for v in Var::new(1)..=self.ts.max_var() {
            if !keep.contains(&v) {
                latch.push(v);
                next.insert(v, self.lit_next(v.lit(), 1));
            }
        }

        // TODO: EXTEND INIT

        Transys {
            input: self.ts.input.clone(),
            latch,
            next,
            init: self.ts.init.clone(),
            bad: self.ts.bad,
            constraint: self.ts.constraint.clone(),
            rel,
            rst: self.ts.rst.clone(),
        }
    }
}
