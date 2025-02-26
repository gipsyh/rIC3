use super::{Transys, TransysIf};
use giputils::hash::GHashMap;
use logic_form::{Cnf, Lit, LitVec, Var};
use satif::Satif;
use std::mem::take;

#[derive(Default, Debug, Clone)]
pub struct NoDepTransys {
    pub input: Vec<Var>,
    pub latch: Vec<Var>,
    pub next: GHashMap<Var, Lit>,
    pub init: GHashMap<Var, bool>,
    pub bad: Lit,
    pub constraint: LitVec,
    pub rel: Cnf,
    pub rst: GHashMap<Var, Var>,
}

impl NoDepTransys {
    pub fn assert_constraint(&mut self) {
        for c in take(&mut self.constraint) {
            self.rel.add_clause(&[c]);
        }
    }

    pub fn simplify(&mut self) {
        let mut simp_solver = cadical::Solver::new();
        simp_solver.new_var_to(self.max_var());
        for c in self.trans() {
            simp_solver.add_clause(c);
        }
        let mut frozens = vec![Var::CONST, self.bad.var()];
        frozens.extend_from_slice(&self.input);
        for &l in self.latch.iter() {
            frozens.push(l);
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
        let domain_map = self.rel.arrange(frozens.into_iter());
        let map_lit = |l: &Lit| Lit::new(domain_map[&l.var()], l.polarity());
        self.input = self.input.iter().map(|v| domain_map[v]).collect();
        self.latch = self.latch.iter().map(|v| domain_map[v]).collect();
        self.init = self.init.iter().map(|(v, i)| (domain_map[v], *i)).collect();
        self.next = self
            .next
            .iter()
            .map(|(v, n)| (domain_map[v], map_lit(n)))
            .collect();
        self.bad = map_lit(&self.bad);
        self.constraint = self.constraint.iter().map(map_lit).collect();
        self.rst = self
            .rst
            .iter()
            .filter_map(|(k, &v)| domain_map.get(k).map(|&dk| (dk, v)))
            .collect();
    }
}

impl TransysIf for NoDepTransys {
    #[inline]
    fn max_var(&self) -> Var {
        self.rel.max_var()
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
        self.next[&lit.var()].not_if(!lit.polarity())
    }

    #[inline]
    fn init(&self) -> impl Iterator<Item = Lit> {
        self.init.iter().map(|(v, i)| Lit::new(*v, *i))
    }

    #[inline]
    fn constraint(&self) -> impl Iterator<Item = Lit> {
        self.constraint.iter().copied()
    }

    #[inline]
    fn trans(&self) -> impl Iterator<Item = &LitVec> {
        self.rel.iter()
    }

    #[inline]
    fn restore(&self, lit: Lit) -> Lit {
        self.rst[&lit.var()].lit().not_if(!lit.polarity())
    }
}

impl Transys {
    pub fn remove_dep(self) -> NoDepTransys {
        NoDepTransys {
            input: self.input,
            latch: self.latch,
            next: self.next,
            init: self.init,
            bad: self.bad,
            constraint: self.constraint,
            rel: self.rel.lower(),
            rst: self.rst,
        }
    }
}
