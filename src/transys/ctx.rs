use super::{Transys, TransysIf};
use giputils::hash::GHashMap;
use logic_form::{DagCnf, Lit, LitMap, LitVec, Var, VarMap};

#[derive(Clone, Default, Debug)]
pub struct TransysCtx {
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
    pub rst: GHashMap<Var, Var>,
}

impl TransysIf for TransysCtx {
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
        self.inputs.iter().copied()
    }

    #[inline]
    fn latch(&self) -> impl Iterator<Item = Var> {
        self.latchs.iter().copied()
    }

    #[inline]
    fn init(&self) -> impl Iterator<Item = Lit> {
        self.init.iter().copied()
    }

    #[inline]
    fn next(&self, lit: Lit) -> Lit {
        self.next_map[lit]
    }

    #[inline]
    fn prev(&self, lit: Lit) -> Lit {
        self.prev_map[lit]
    }

    #[inline]
    fn constraint(&self) -> impl Iterator<Item = Lit> {
        self.constraints.iter().copied()
    }

    #[inline]
    fn trans(&self) -> impl Iterator<Item = &LitVec> {
        self.rel.clause()
    }

    #[inline]
    fn restore(&self, lit: Lit) -> Option<Lit> {
        self.rst
            .get(&lit.var())
            .map(|v| v.lit().not_if(!lit.polarity()))
    }
}

impl TransysCtx {
    #[inline]
    pub fn num_var(&self) -> usize {
        Into::<usize>::into(self.max_var()) + 1
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
            .map(|c| c.iter().map(|l| self.next(*l)).collect())
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
    pub fn cube_subsume_init(&self, x: &[Lit]) -> bool {
        for x in x {
            if let Some(init) = self.init_map[x.var()]
                && init != x.polarity()
            {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn is_latch(&self, var: Var) -> bool {
        self.is_latch[var]
    }
}

impl Transys {
    pub fn ctx(mut self) -> TransysCtx {
        self.latch.sort();
        let primes: Vec<Lit> = self.latch.iter().map(|l| self.next(l.lit())).collect();
        let max_var = self.rel.max_var();
        let max_latch = *self.latch.iter().max().unwrap_or(&Var::CONST);
        let mut init_map = VarMap::new_with(max_latch);
        let mut is_latch = VarMap::new_with(max_var);
        let mut init = LitVec::new();
        let mut next_map = LitMap::new_with(max_latch);
        let mut prev_map = LitMap::new_with(max_var);
        for (v, p) in self.latch.iter().cloned().zip(primes.iter().cloned()) {
            let l = v.lit();
            let i = self.init.get(&v).cloned();
            if let Some(i) = i {
                init_map[v] = Some(i);
                init.push(l.not_if(!i));
            }
            next_map[l] = p;
            next_map[!l] = !p;
            prev_map[p] = l;
            prev_map[!p] = !l;
            is_latch[v] = true;
        }
        TransysCtx {
            inputs: self.input,
            latchs: self.latch,
            init,
            bad: self.bad[0],
            init_map,
            constraints: self.constraint,
            rel: self.rel,
            is_latch,
            next_map,
            prev_map,
            max_latch,
            rst: self.rst,
        }
    }
}
