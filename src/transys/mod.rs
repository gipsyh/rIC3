mod aux;
pub mod certify;
mod ctx;
pub mod frts;
pub mod lift;
mod live;
pub mod nodep;
mod others;
mod refactor;
pub mod scorr;
mod simp;
mod simulate;
pub mod unroll;

pub use ctx::*;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::{DagCnf, Lit, LitVec, LitVvec, Var, VarVMap, satif::Satif};
use std::{
    fmt::{self, Display},
    mem::take,
};

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

    fn is_latch(&self, _v: Var) -> bool {
        panic!("Error: is_latch not support");
    }

    fn next(&self, lit: Lit) -> Lit;

    fn init(&self, latch: Var) -> Option<Lit>;

    fn constraint(&self) -> impl Iterator<Item = Lit>;

    fn trans(&self) -> impl Iterator<Item = &LitVec>;

    #[inline]
    fn var_next(&self, var: Var) -> Var {
        self.next(var.lit()).var()
    }

    #[inline]
    fn lits_next<'a>(&self, lits: impl IntoIterator<Item = &'a Lit>) -> LitVec {
        lits.into_iter().map(|l| self.next(*l)).collect()
    }

    fn inits(&self) -> LitVvec {
        let mut cnf = LitVvec::new();
        for l in self.latch() {
            if let Some(i) = self.init(l) {
                if let Some(i) = i.try_constant() {
                    cnf.push(LitVec::from([l.lit().not_if(!i)]));
                } else {
                    cnf.push(LitVec::from([l.lit(), !i]));
                    cnf.push(LitVec::from([!l.lit(), i]));
                }
            }
        }
        cnf
    }

    #[inline]
    fn load_init<S: Satif + ?Sized>(&self, satif: &mut S) {
        satif.new_var_to(self.max_var());
        for cls in self.inits() {
            satif.add_clause(&cls);
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
    fn statistic(&self) -> String {
        format!(
            "{} vars, {} inputs, {} latches, {} clauses, {} constraints",
            self.max_var(),
            self.input().count(),
            self.latch().count(),
            self.trans().count(),
            self.constraint().count(),
        )
    }

    fn add_input(&mut self, _input: Var) {
        panic!("Error: add input not support");
    }

    fn add_latch(&mut self, _latch: Var, _init: Option<Lit>, _next: Lit) {
        panic!("Error: add latch not support");
    }

    fn add_init(&mut self, _latch: Var, _init: Lit) {
        panic!("Error: add init not support");
    }
}

#[derive(Default, Debug, Clone)]
pub struct Transys {
    pub input: Vec<Var>,
    pub latch: Vec<Var>,
    pub next: GHashMap<Var, Lit>,
    pub init: GHashMap<Var, Lit>,
    /// multiple bads, not single cube
    pub bad: LitVec,
    pub constraint: LitVec,
    pub justice: LitVec,
    pub rel: DagCnf,
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
    fn is_latch(&self, v: Var) -> bool {
        self.next.contains_key(&v)
    }

    #[inline]
    fn next(&self, lit: Lit) -> Lit {
        self.next.get(&lit.var()).unwrap().not_if(!lit.polarity())
    }

    fn init(&self, latch: Var) -> Option<Lit> {
        self.init.get(&latch).copied()
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
    fn add_input(&mut self, input: Var) {
        self.input.push(input);
    }

    #[inline]
    fn add_latch(&mut self, latch: Var, init: Option<Lit>, next: Lit) {
        self.latch.push(latch);
        self.next.insert(latch, next);
        if let Some(i) = init {
            self.init.insert(latch, i);
        }
    }

    #[inline]
    fn add_init(&mut self, latch: Var, init: Lit) {
        self.init.insert(latch, init);
    }
}

impl Transys {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn unique_prime(&mut self, rst: &mut VarVMap) {
        let mut unique = GHashSet::new();
        unique.insert(Var::CONST);
        for l in self.latch.clone() {
            let mut n = self.next[&l];
            if unique.contains(&n.var()) {
                let u = self.rel.new_var().lit();
                self.rel.add_rel(u.var(), &LitVvec::cnf_assign(u, n));
                self.next.insert(l, u);
                if let Some(&r) = rst.get(&n.var()) {
                    rst.insert(u.var(), r);
                }
                n = u;
            }
            unique.insert(n.var());
        }
    }

    pub fn add_init_var(&mut self) -> Var {
        let iv = self.new_var();
        self.add_latch(iv, Some(Lit::constant(true)), Lit::constant(false));
        iv
    }

    pub fn compress_bads(&mut self) {
        if self.bad.len() <= 1 {
            return;
        }
        let bad = take(&mut self.bad);
        self.bad = LitVec::from(self.rel.new_or(bad));
    }
}

impl Display for Transys {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "input: {:?}", self.input)?;
        for l in self.latch.iter() {
            if let Some(i) = self.init.get(l) {
                writeln!(f, "latch {l}, next {}, init {i}", self.next(l.lit()))?;
            } else {
                writeln!(f, "latch {l}, next {}", self.var_next(*l))?;
            }
        }
        writeln!(f, "rel:")?;
        self.rel.fmt(f)?;
        writeln!(f, "bad: {:?}", self.bad)?;
        writeln!(f, "constraint: {:?}", self.constraint)
    }
}
