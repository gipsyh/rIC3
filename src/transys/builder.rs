use super::Transys;
use aig::Aig;
use dagcnf::DagCnf;
use giputils::hash::GHashMap;
use logic_form::{Lit, LitMap, LitVec, LitVvec, Var, VarMap};

#[derive(Default, Debug, Clone)]
pub struct TransysBuilder {
    pub input: Vec<Var>,
    pub latch: Vec<Var>,
    pub next: GHashMap<Var, Lit>,
    pub init: GHashMap<Var, bool>,
    pub bad: Lit,
    pub constraint: LitVec,
    pub rel: DagCnf,
    pub rst: GHashMap<Var, Var>,
}

impl TransysBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn max_var(&self) -> Var {
        self.rel.max_var()
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit) -> Lit {
        self.next[&lit.var()].not_if(!lit.polarity())
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

    pub fn build(mut self) -> Transys {
        self.latch.sort();
        let primes: Vec<Lit> = self
            .latch
            .iter()
            .map(|l| self.rel.new_var().lit().not_if(!self.next[l].polarity()))
            .collect();
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
            let n = self.next[&v];
            self.rel.add_rel(p.var(), &LitVvec::cnf_assign(p, n));
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
        for (l, p) in self.latch.iter().zip(primes.iter()) {
            let n = self.next[l];
            assert!(p.polarity() == n.polarity());
            if let Some(r) = self.rst.get(&n.var()).cloned() {
                self.rst.insert(p.var(), r);
            }
        }
        Transys {
            inputs: self.input,
            latchs: self.latch,
            init,
            bad: self.bad,
            init_map,
            constraints: self.constraint,
            rel: self.rel,
            is_latch,
            next_map,
            prev_map,
            max_latch,
            restore: self.rst,
        }
    }
}
