use super::{Transys, TransysIf};
use crate::transys::certify::Restore;
use giputils::hash::GHashMap;
use logicrs::{Cnf, Lit, LitVec, Var, satif::Satif};
use std::mem::take;

#[derive(Default, Debug, Clone)]
pub struct NoDepTransys {
    pub input: Vec<Var>,
    pub latch: Vec<Var>,
    pub next: GHashMap<Var, Lit>,
    pub init: GHashMap<Var, Lit>,
    pub bad: Lit,
    pub constraint: LitVec,
    pub rel: Cnf,
}

impl NoDepTransys {
    pub fn assert_constraint(&mut self) {
        for c in take(&mut self.constraint) {
            self.rel.add_clause(&[c]);
        }
    }

    pub fn simplify(&mut self, rst: &mut Restore) {
        let mut simp_solver = cadical::CaDiCaL::new();
        simp_solver.new_var_to(self.max_var());
        for c in self.trans() {
            simp_solver.add_clause(c);
        }
        let mut frozens = vec![Var::CONST, self.bad.var()];
        frozens.extend(self.input.iter().chain(self.latch.iter()).copied());
        for &l in self.latch.iter() {
            if let Some(i) = self.init(l) {
                frozens.push(i.var());
            }
            frozens.push(self.var_next(l));
        }
        for c in self.constraint.iter() {
            frozens.push(c.var());
        }
        for f in frozens.iter() {
            simp_solver.set_frozen(*f, true);
        }
        if let Some(false) = simp_solver.simplify() {
            println!("warning: model trans simplified with unsat");
        }
        let mut trans = simp_solver.clauses();
        trans.push(LitVec::from([Lit::constant(true)]));
        self.rel.set_cls(trans);
        let domain_map = self.rel.rearrange(frozens);
        let map_lit = |l: &Lit| Lit::new(domain_map[l.var()], l.polarity());
        self.input = self.input.iter().map(|&v| domain_map[v]).collect();
        self.latch = self.latch.iter().map(|&v| domain_map[v]).collect();
        self.init = self
            .init
            .iter()
            .map(|(v, i)| (domain_map[*v], map_lit(i)))
            .collect();
        self.next = self
            .next
            .iter()
            .map(|(v, n)| (domain_map[*v], map_lit(n)))
            .collect();
        self.bad = map_lit(&self.bad);
        self.constraint = self.constraint.iter().map(map_lit).collect();
        rst.filter_map_var(|v| domain_map.get(&v).copied());
    }
}

impl TransysIf for NoDepTransys {
    #[inline]
    fn max_var(&self) -> Var {
        self.rel.max_var()
    }

    #[inline]
    fn new_var(&mut self) -> Var {
        self.rel.new_var()
    }

    #[inline]
    fn input(&self) -> impl Iterator<Item = Var> {
        self.input.iter().copied()
    }

    #[inline]
    fn latch(&self) -> impl Iterator<Item = Var> {
        self.latch.iter().copied()
    }

    #[inline]
    fn next(&self, lit: Lit) -> Lit {
        self.next.get(&lit.var()).unwrap().not_if(!lit.polarity())
    }

    #[inline]
    fn init(&self, latch: Var) -> Option<Lit> {
        self.init.get(&latch).copied()
    }

    #[inline]
    fn constraint(&self) -> impl Iterator<Item = Lit> {
        self.constraint.iter().copied()
    }

    #[inline]
    fn trans(&self) -> impl Iterator<Item = &LitVec> {
        self.rel.iter()
    }
}

impl Transys {
    pub fn remove_dep(self) -> NoDepTransys {
        assert!(self.bad.len() == 1);
        NoDepTransys {
            input: self.input,
            latch: self.latch,
            next: self.next,
            init: self.init,
            bad: self.bad[0],
            constraint: self.constraint,
            rel: self.rel.lower(),
        }
    }
}
