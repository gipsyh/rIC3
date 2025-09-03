use super::{Transys, TransysIf};
use crate::transys::certify::Restore;
use giputils::hash::GHashMap;
use logicrs::{Lit, LitVec, Var, VarLMap};
use std::mem::take;

impl Transys {
    pub fn frozens(&self) -> Vec<Var> {
        let mut frozens = vec![Var::CONST];
        frozens.extend(
            self.bad
                .iter()
                .chain(self.constraint.iter())
                .chain(self.justice.iter())
                .map(|l| l.var())
                .chain(self.input.iter().copied())
                .chain(self.latch.iter().copied()),
        );
        for l in self.latch.iter() {
            if let Some(i) = self.init.get(l) {
                frozens.push(i.var());
            }
            if let Some(n) = self.next.get(l) {
                frozens.push(n.var());
            }
        }
        frozens
    }

    pub fn merge(&mut self, other: &Self) {
        let offset = self.max_var();
        let map = |x: Var| {
            if x == Var::CONST { x } else { x + offset }
        };
        self.new_var_to(map(other.max_var()));
        let lmap = |x: Lit| Lit::new(map(x.var()), x.polarity());
        for v in Var(1)..=other.max_var() {
            let rel: Vec<LitVec> = other.rel[v]
                .iter()
                .map(|cls| cls.iter().map(|l| lmap(*l)).collect())
                .collect();
            let mv = map(v);
            self.rel.add_rel(mv, &rel);
        }
        for i in other.input.iter() {
            self.input.push(map(*i));
        }
        for &l in other.latch.iter() {
            let ml = map(l);
            self.latch.push(ml);
            self.next.insert(ml, lmap(other.next[&l]));
            if let Some(i) = other.init.get(&l) {
                self.init.insert(ml, lmap(*i));
            }
        }
        let mut bad = self.bad.clone();
        bad.extend(other.bad.map(lmap));
        self.bad = LitVec::from(self.rel.new_or(bad));
        for &l in other.constraint.iter() {
            self.constraint.push(lmap(l));
        }
        for &l in other.justice.iter() {
            self.justice.push(lmap(l));
        }
    }

    pub fn remove_gate_init(&mut self, rst: &mut Restore) {
        let mut init = GHashMap::new();
        let mut eq = Vec::new();
        for l in self.input().chain(self.latch()) {
            if let Some(i) = self.init.get(&l).copied() {
                if i.try_constant().is_some() {
                    init.insert(l, i);
                } else {
                    eq.push((l, i));
                }
            }
        }
        if eq.is_empty() {
            return;
        }
        self.init = init;
        let iv = self.add_init_var();
        rst.set_init_var(iv);
        for (v, i) in eq {
            let e = self.rel.new_xnor(v.lit(), i);
            let c = self.rel.new_imply(iv.lit(), e);
            self.constraint.push(c);
            // rst.add_custom_constraint(c);
        }
    }

    pub fn map(&mut self, map: impl Fn(Var) -> Var + Copy, rst: &mut Restore) {
        self.input
            .iter_mut()
            .chain(self.latch.iter_mut())
            .for_each(|v| *v = map(*v));
        self.rel = self.rel.map(map);
        for (k, v) in take(&mut self.init) {
            self.init.insert(map(k), v.map_var(map));
        }
        for (k, v) in take(&mut self.next) {
            self.next.insert(map(k), v.map_var(map));
        }
        self.bad = self.bad.map_var(map);
        self.constraint = self.constraint.map_var(map);
        self.justice = self.justice.map_var(map);
        rst.map_var(map);
    }

    pub fn replace(&mut self, map: &VarLMap, rst: &mut Restore) {
        for (&x, &y) in map.iter() {
            if self.is_latch(x) {
                rst.replace(x, y);
            } else {
                rst.remove(x);
            }
        }
        self.input.retain(|l| !map.contains_key(l));
        self.latch.retain(|l| !map.contains_key(l));
        self.init.retain(|l, _| !map.contains_key(l));
        self.next.retain(|l, _| !map.contains_key(l));
        self.rel.replace(map);
        for l in self.next.values_mut().chain(self.init.values_mut()) {
            if let Some(m) = map.map_lit(*l) {
                *l = m;
            }
        }
        let map_fn = map.try_map_fn();
        self.bad = self.bad.map(|l| map_fn(l).unwrap_or(l));
        self.constraint = self.constraint.map(|l| map_fn(l).unwrap_or(l));
        self.justice = self.justice.map(|l| map_fn(l).unwrap_or(l));
    }

    pub fn topsort(&mut self, rst: &mut Restore) {
        let (_, m) = self.rel.topsort();
        let m = m.inverse();
        self.map(|v| m[v], rst);
    }

    // pub fn add_init_var(&mut self) -> Var {
    //     let iv = self.new_var();
    //     self.add_latch(iv, Some(Lit::constant(true)), Lit::constant(false));
    //     iv
    // }
}
