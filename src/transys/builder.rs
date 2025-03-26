use super::Transys;
use logic_form::{Cube, DagCnf, Lit, LitMap, Var, VarMap};
use std::{collections::HashMap, iter::repeat_with};

#[derive(Default, Debug)]
pub struct TransysBuilder {
    pub input: Vec<Var>,
    pub latch: HashMap<Var, (Option<bool>, Lit)>,
    pub bad: Lit,
    pub constraint: Cube,
    pub rel: DagCnf,
}

impl TransysBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn build(mut self) -> Transys {
        let mut latchs: Vec<_> = self.latch.keys().cloned().collect();
        latchs.sort();
        let primes: Vec<_> = repeat_with(|| self.rel.new_var().lit())
            .take(latchs.len())
            .collect();
        let max_var = self.rel.max_var;
        let max_latch = *latchs.iter().max().unwrap_or(&Var::new(0));
        let mut init_map = VarMap::new_with(max_latch);
        let mut is_latch = VarMap::new_with(max_var);
        let mut init = Cube::new();
        let mut next_map = LitMap::new_with(max_latch);
        let mut prev_map = LitMap::new_with(max_var);
        for (v, p) in latchs.iter().cloned().zip(primes) {
            let l = v.lit();
            let (i, n) = self.latch.get(&v).unwrap().clone();
            self.rel.add_assign_rel(p, n);
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
        Transys {
            inputs: self.input,
            latchs,
            init,
            bad: self.bad,
            init_map,
            constraints: self.constraint,
            trans: self.rel.cnf,
            max_var: self.rel.max_var,
            is_latch,
            next_map,
            prev_map,
            dependence: self.rel.dep,
            max_latch,
            restore: Default::default(),
        }
    }
}
