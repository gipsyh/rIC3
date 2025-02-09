use super::Transys;
use aig::Aig;
use giputils::hash::GHashMap;
use logic_form::{DagCnf, Lit, LitMap, LitVec, Var, VarMap};

#[derive(Default, Debug)]
pub struct TransysBuilder {
    pub input: Vec<Var>,
    pub latch: GHashMap<Var, (Option<bool>, Lit)>,
    pub bad: Lit,
    pub constraint: LitVec,
    pub rel: DagCnf,
    pub rst: GHashMap<Var, Var>,
}

impl TransysBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_aig(aig: &Aig, rst: &GHashMap<Var, Var>) -> Self {
        let input: Vec<Var> = aig.inputs.iter().map(|x| Var::new(*x)).collect();
        let constraint: LitVec = aig.constraints.iter().map(|c| c.to_lit()).collect();
        let mut latch = GHashMap::new();
        for l in aig.latchs.iter() {
            latch.insert(Var::from(l.input), (l.init, l.next.to_lit()));
        }
        let bad = aig.bads[0].to_lit();
        let rel = aig.get_cnf();
        Self {
            input,
            latch,
            bad,
            constraint,
            rel,
            rst: rst.clone(),
        }
    }

    pub fn build(mut self) -> Transys {
        let mut latchs: Vec<_> = self.latch.keys().cloned().collect();
        latchs.sort();
        let primes: Vec<Lit> = latchs
            .iter()
            .map(|l| {
                let next = self.latch.get(l).unwrap().1;
                self.rel.new_var().lit().not_if(!next.polarity())
            })
            .collect();
        let max_var = self.rel.max_var();
        let max_latch = *latchs.iter().max().unwrap_or(&Var::new(0));
        let mut init_map = VarMap::new_with(max_latch);
        let mut is_latch = VarMap::new_with(max_var);
        let mut init = LitVec::new();
        let mut next_map = LitMap::new_with(max_latch);
        let mut prev_map = LitMap::new_with(max_var);
        for (v, p) in latchs.iter().cloned().zip(primes.iter().cloned()) {
            let l = v.lit();
            let (i, n) = *self.latch.get(&v).unwrap();
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
        for (l, p) in latchs.iter().zip(primes.iter()) {
            let n = self.latch[l].1;
            assert!(p.polarity() == n.polarity());
            if let Some(r) = self.rst.get(&n.var()).cloned() {
                self.rst.insert(p.var(), r);
            }
        }
        Transys {
            inputs: self.input,
            latchs,
            init,
            bad: self.bad,
            init_map,
            constraints: self.constraint,
            trans: self.rel.cnf.to_vec(),
            max_var: self.rel.max_var(),
            is_latch,
            next_map,
            prev_map,
            dependence: self.rel.dep,
            max_latch,
            restore: self.rst.clone(),
        }
    }
}
