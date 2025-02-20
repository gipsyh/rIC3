pub mod builder;
pub mod simplify;
pub mod simulate;
pub mod unroll;
pub mod uunroll;

use dagcnf::DagCnf;
use giputils::hash::GHashMap;
use logic_form::{Lit, LitMap, LitVec, Var, VarMap};
use satif::Satif;

#[derive(Clone, Default, Debug)]
pub struct Transys {
    pub inputs: Vec<Var>,
    pub latchs: Vec<Var>,
    pub init: LitVec,
    pub bad: Lit,
    pub init_map: VarMap<Option<bool>>,
    pub constraints: LitVec,
    pub rel: DagCnf,
    is_latch: VarMap<bool>,
    next_map: LitMap<Lit>,
    prev_map: LitMap<Lit>,
    pub max_latch: Var,
    restore: GHashMap<Var, Var>,
}

impl Transys {
    #[inline]
    pub fn num_var(&self) -> usize {
        Into::<usize>::into(self.max_var()) + 1
    }

    #[inline]
    pub fn max_var(&self) -> Var {
        self.rel.max_var()
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        let max_var = self.rel.new_var();
        self.init_map.reserve(max_var);
        self.next_map.reserve(max_var);
        self.prev_map.reserve(max_var);
        self.is_latch.reserve(max_var);
        max_var
    }

    #[inline]
    pub fn add_latch(&mut self, state: Var, init: Option<bool>, trans: Vec<LitVec>) {
        let next = self.rel.new_var().lit();
        self.latchs.push(state);
        let lit = state.lit();
        self.init_map[state] = init;
        self.is_latch[state] = true;
        self.next_map[lit] = next;
        self.next_map[!lit] = !next;
        self.prev_map[next] = lit;
        self.prev_map[!next] = !lit;
        if let Some(i) = init {
            self.init.push(lit.not_if(!i));
        }
        self.rel.add_rel(state, &trans);
        let next_trans: Vec<_> = trans
            .iter()
            .map(|c| c.iter().map(|l| self.lit_next(*l)).collect())
            .collect();
        self.rel.add_rel(next.var(), &next_trans);
    }

    pub fn add_init(&mut self, v: Var, init: Option<bool>) {
        assert!(self.is_latch(v));
        self.init_map[v] = init;
        if let Some(i) = init {
            self.init.push(v.lit().not_if(!i));
        }
    }

    #[inline]
    pub fn var_next(&self, var: Var) -> Var {
        self.next_map[var.lit()].var()
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit) -> Lit {
        self.next_map[lit]
    }

    #[inline]
    pub fn lit_prev(&self, lit: Lit) -> Lit {
        self.prev_map[lit]
    }

    #[inline]
    pub fn cube_next(&self, cube: &[Lit]) -> LitVec {
        cube.iter().map(|l| self.lit_next(*l)).collect()
    }

    #[inline]
    pub fn cube_prev(&self, cube: &[Lit]) -> LitVec {
        cube.iter().map(|l| self.lit_prev(*l)).collect()
    }

    #[inline]
    pub fn cube_subsume_init(&self, x: &[Lit]) -> bool {
        for x in x {
            if let Some(init) = self.init_map[x.var()] {
                if init != x.polarity() {
                    return false;
                }
            }
        }
        true
    }

    #[inline]
    pub fn is_latch(&self, var: Var) -> bool {
        self.is_latch[var]
    }

    pub fn load_init<S: Satif + ?Sized>(&self, satif: &mut S) {
        satif.new_var_to(self.max_var());
        for i in self.init.iter() {
            satif.add_clause(&[*i]);
        }
    }

    pub fn load_trans(&self, satif: &mut impl Satif, constraint: bool) {
        satif.new_var_to(self.max_var());
        for c in self.rel.iter() {
            satif.add_clause(c);
        }
        if constraint {
            for c in self.constraints.iter() {
                satif.add_clause(&[*c]);
            }
        }
    }

    #[inline]
    pub fn restore(&self, lit: Lit) -> Lit {
        let var = self.restore[&lit.var()];
        Lit::new(var, lit.polarity())
    }

    pub fn print_info(&self) {
        println!("num input: {}", self.inputs.len());
        println!("num latch: {}", self.latchs.len());
        println!("trans size: {}", self.rel.len());
        println!("num constraint: {}", self.constraints.len());
    }
}
