use super::DagCnf;
use crate::Lit;
use crate::{Var, VarMap, VarRange};
use giputils::bitvec::BitVec;
use giputils::hash::GHashSet;
use rand::SeedableRng;
use rand::rngs::StdRng;
use std::ops::Index;

#[derive(Clone, Debug)]
pub struct DagCnfSimulation {
    pub(crate) sim: VarMap<BitVec>,
}

impl Index<Var> for DagCnfSimulation {
    type Output = BitVec;

    #[inline]
    fn index(&self, var: Var) -> &Self::Output {
        &self.sim[var]
    }
}

impl DagCnfSimulation {
    #[inline]
    pub fn val(&self, lit: Lit) -> BitVec {
        if !lit.polarity() {
            !&self.sim[lit.var()]
        } else {
            self.sim[lit.var()].clone()
        }
    }

    fn simulate_var(&mut self, v: Var, dc: &DagCnf) {
        for rel in dc.cnf[v].iter() {
            let mut sim = self.val(rel[0]);
            let mut vl = rel[0];
            for &l in &rel[1..] {
                if l.var() == v {
                    vl = l;
                }
                if l.polarity() {
                    sim |= &self[l.var()];
                } else {
                    sim |= &!&self[l.var()];
                }
            }
            assert!(vl.var() == v);
            if vl.polarity() {
                self.sim[v] |= &!&sim;
            } else {
                self.sim[v] &= &sim;
            }
        }
    }

    pub fn simulate(&mut self, dc: &DagCnf) {
        for v in VarRange::new_inclusive(Var(1), dc.max_var()) {
            if dc.is_leaf(v) {
                continue;
            }
            self.simulate_var(v, dc);
        }
    }

    #[inline]
    pub fn add(&mut self, val: BitVec) {
        assert!(self.sim.len() == val.len());
        for v in 0..val.len() {
            self.sim[Var(v as u32)].push(val.get(v));
        }
    }
}

impl DagCnf {
    pub fn simulation(&self, num_word: usize) -> DagCnfSimulation {
        let mut rng = StdRng::seed_from_u64(0);
        let mut sim = VarMap::new_with(self.max_var());
        sim[Var::CONST] = BitVec::from_elem(num_word * BitVec::WORD_SIZE, false);
        let mut leafs = GHashSet::new();
        for v in VarRange::new_inclusive(Var(1), self.max_var()) {
            if self.is_leaf(v) {
                loop {
                    let x = BitVec::new_rand(num_word, &mut rng);
                    if !leafs.contains(&x) {
                        leafs.insert(x.clone());
                        sim[v] = x;
                        break;
                    }
                }
            } else {
                sim[v] = BitVec::from_elem(num_word * BitVec::WORD_SIZE, false);
            }
        }
        let mut s = DagCnfSimulation { sim };
        s.simulate(self);
        s
    }
}
