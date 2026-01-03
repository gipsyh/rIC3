use super::{Transys, TransysIf};
use crate::transys::certify::Restore;
use giputils::hash::GHashMap;
use logicrs::{Lit, LitVec, Var, VarLMap, VarRange};
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

    pub fn merge(&mut self, other: &Self, mapf: impl Fn(Var) -> Option<Var>) {
        let begin = self.max_var();
        let mut vmap = GHashMap::new();
        assert!(mapf(Var::CONST) == Some(Var::CONST));
        for v in VarRange::new_inclusive(Var::CONST, other.max_var()) {
            let m = if let Some(m) = mapf(v) {
                m
            } else {
                self.new_var()
            };
            vmap.insert(v, m);
        }
        let lmap = |x: Lit| x.map_var(|v| vmap[&v]);
        for i in other.input.iter() {
            let m = vmap[i];
            if m > begin {
                self.input.push(m);
            }
        }
        for l in other.latch.iter() {
            let ml = vmap[l];
            if ml <= begin {
                continue;
            }
            self.latch.push(ml);
            self.next.insert(ml, lmap(other.next[l]));
            if let Some(i) = other.init.get(l) {
                self.init.insert(ml, lmap(*i));
            }
        }
        for v in VarRange::new_inclusive(Var::CONST, other.max_var()) {
            let mv = vmap[&v];
            if mv <= begin {
                continue;
            }
            let rel: Vec<LitVec> = other.rel[v]
                .iter()
                .map(|cls| cls.iter().map(|l| lmap(*l)).collect())
                .collect();
            self.rel.add_rel(mv, &rel);
        }
        for &l in other.bad.iter() {
            let lm = lmap(l);
            if lm.var() > begin {
                self.bad.push(lm);
            }
        }
        for &l in other.constraint.iter() {
            let lm = lmap(l);
            if lm.var() > begin {
                self.constraint.push(lm);
            }
        }
        for &l in other.justice.iter() {
            let lm = lmap(l);
            if lm.var() > begin {
                self.justice.push(lm);
            }
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
        let iv = rst.get_init_var(self);
        for (v, i) in eq {
            let e = self.rel.new_xnor(v.lit(), i);
            let c = self.rel.new_imply(iv.lit(), e);
            self.constraint.push(c);
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
        rst.map_var(&map);
    }

    pub fn replace(&mut self, map: &VarLMap, rst: &mut Restore) {
        for (&x, &y) in map.iter() {
            if self.is_latch(x)
                && let Some(x_init) = self.init(x)
            {
                let y_init = x_init.not_if(!y.polarity());
                if let Some(init) = self.init.get_mut(&y.var()) {
                    let c = self.rel.new_xnor(*init, y_init);
                    if !c.is_constant(true) {
                        let iv = rst.get_init_var(self);
                        let c = self.rel.new_imply(iv.lit(), c);
                        self.constraint.push(c);
                    }
                } else {
                    self.init.insert(y.var(), y_init);
                }
            }
        }
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
}
