mod ctx;
pub mod nodep;
pub mod unroll;

use aig::Aig;
pub use ctx::*;
use giputils::hash::GHashMap;
use logic_form::{DagCnf, Lit, LitVec, Var};
use satif::Satif;

pub trait TransysIf {
    fn max_var(&self) -> Var;

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

    pub fn from_aig(aig: &Aig, rst: &GHashMap<Var, Var>) -> Self {
        let input: Vec<Var> = aig.inputs.iter().map(|x| Var::new(*x)).collect();
        let constraint: LitVec = aig.constraints.iter().map(|c| c.to_lit()).collect();
        let mut latch = Vec::new();
        let mut next = GHashMap::new();
        let mut init = GHashMap::new();
        for l in aig.latchs.iter() {
            let lv = Var::from(l.input);
            latch.push(lv);
            next.insert(lv, l.next.to_lit());
            if let Some(i) = l.init {
                init.insert(lv, i);
            }
        }
        let bad = aig.bads[0].to_lit();
        let rel = aig.get_cnf();
        Self {
            input,
            latch,
            next,
            init,
            bad,
            constraint,
            rel,
            rst: rst.clone(),
        }
    }

    pub fn simplify(&mut self) {
        let mut frozens = vec![Var::CONST, self.bad.var()];
        frozens.extend_from_slice(&self.input);
        for l in self.latch.iter() {
            frozens.push(*l);
            frozens.push(self.next[l].var());
        }
        for c in self.constraint.iter() {
            frozens.push(c.var());
        }
        self.rel = self.rel.simplify(frozens.iter().copied());
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
