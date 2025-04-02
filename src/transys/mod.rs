mod ctx;
pub mod nodep;
mod others;
mod simp;
pub mod unroll;

pub use ctx::*;
use giputils::hash::{GHashMap, GHashSet};
use logic_form::{DagCnf, Lit, LitVec, LitVvec, Var};
use satif::Satif;

pub trait TransysIf {
    fn max_var(&self) -> Var;

    fn new_var(&mut self) -> Var;

    #[inline]
    fn new_var_to(&mut self, var: Var) {
        while self.max_var() < var {
            self.new_var();
        }
    }

    fn input(&self) -> impl Iterator<Item = Var>;

    fn latch(&self) -> impl Iterator<Item = Var>;

    fn next(&self, lit: Lit) -> Lit;

    fn prev(&self, _lit: Lit) -> Lit {
        panic!("prev not supported");
    }

    fn init(&self) -> impl Iterator<Item = Lit>;

    fn constraint(&self) -> impl Iterator<Item = Lit>;

    fn trans(&self) -> impl Iterator<Item = &LitVec>;

    fn restore(&self, lit: Lit) -> Lit;

    #[inline]
    fn var_next(&self, var: Var) -> Var {
        self.next(var.lit()).var()
    }

    #[inline]
    fn lits_next<'a>(&self, lits: impl IntoIterator<Item = &'a Lit>) -> LitVec {
        lits.into_iter().map(|l| self.next(*l)).collect()
    }

    #[inline]
    fn lits_prev<'a>(&self, lits: impl IntoIterator<Item = &'a Lit>) -> LitVec {
        lits.into_iter().map(|l| self.prev(*l)).collect()
    }

    #[inline]
    fn load_init<S: Satif + ?Sized>(&self, satif: &mut S) {
        satif.new_var_to(self.max_var());
        for i in self.init() {
            satif.add_clause(&[i]);
        }
    }

    #[inline]
    fn load_trans(&self, satif: &mut impl Satif, constraint: bool) {
        satif.new_var_to(self.max_var());
        for c in self.trans() {
            satif.add_clause(c);
        }
        if constraint {
            for c in self.constraint() {
                satif.add_clause(&[c]);
            }
        }
    }

    #[inline]
    fn print_info(&self) {
        println!("num input: {}", self.input().count());
        println!("num latch: {}", self.latch().count());
        println!("trans size: {}", self.trans().flatten().count());
        println!("num constraint: {}", self.constraint().count());
    }
}

#[derive(Default, Debug, Clone)]
pub struct Transys {
    pub input: Vec<Var>,
    pub latch: Vec<Var>,
    pub next: GHashMap<Var, Lit>,
    pub init: GHashMap<Var, bool>,
    pub bad: Lit,
    pub constraint: LitVec,
    pub rel: DagCnf,
    pub rst: GHashMap<Var, Var>,
}

impl TransysIf for Transys {
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
        self.rel.clause()
    }

    #[inline]
    fn restore(&self, lit: Lit) -> Lit {
        self.rst[&lit.var()].lit().not_if(!lit.polarity())
    }
}

impl Transys {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn unique_prime(&mut self) {
        let mut unique = GHashSet::new();
        unique.insert(Var::CONST);
        for l in self.latch.clone() {
            let mut n = self.next[&l];
            if unique.contains(&n.var()) {
                let u = self.rel.new_var().lit();
                self.rel.add_rel(u.var(), &LitVvec::cnf_assign(u, n));
                self.next.insert(l, u);
                if let Some(&r) = self.rst.get(&n.var()) {
                    self.rst.insert(u.var(), r);
                }
                n = u;
            }
            unique.insert(n.var());
        }
    }
}
