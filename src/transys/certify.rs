use crate::transys::{Transys, TransysIf};
use giputils::hash::GHashMap;
use logicrs::{Lit, LitVec, LitVvec, Var, VarVMap};
use std::mem::take;

#[derive(Clone, Debug, Default)]
pub struct Witness {
    pub input: Vec<LitVec>,
    pub state: Vec<LitVec>,
}

impl Witness {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[allow(clippy::len_without_is_empty)]
    #[inline]
    pub fn len(&self) -> usize {
        self.input.len()
    }

    pub fn map_var(&self, f: impl Fn(Var) -> Var) -> Self {
        let input = self.input.iter().map(|w| w.map_var(&f)).collect();
        let state = self.state.iter().map(|w| w.map_var(&f)).collect();
        Self { input, state }
    }

    pub fn filter_map_var(&self, f: impl Fn(Var) -> Option<Var>) -> Self {
        let input = self.input.iter().map(|w| w.filter_map_var(&f)).collect();
        let state = self.state.iter().map(|w| w.filter_map_var(&f)).collect();
        Self { input, state }
    }

    pub fn concat(iter: impl IntoIterator<Item = Witness>) -> Self {
        let mut res = Self::new();
        for witness in iter {
            res.input.extend(witness.input);
            res.state.extend(witness.state);
        }
        res
    }
}

#[derive(Clone, Debug, Default)]
pub struct Proof {
    pub proof: Transys,
}

#[derive(Debug, Clone)]
pub struct Restore {
    pub vmap: VarVMap,
    pub eqmap: GHashMap<Var, LitVec>,
}

impl Restore {
    pub fn new(ts: &Transys) -> Self {
        Self {
            vmap: VarVMap::new_self_map(ts.max_var()),
            eqmap: GHashMap::default(),
        }
    }

    pub fn restore(&self, l: Lit) -> Lit {
        self.vmap.lit_map(l).unwrap()
    }

    pub fn restore_var(&self, v: Var) -> Var {
        self.vmap[v]
    }

    #[inline]
    pub fn remove(&mut self, v: Var) {
        self.vmap.remove(&v);
        self.eqmap.remove(&v);
    }

    #[inline]
    pub fn map_var(&mut self, map: impl Fn(Var) -> Var) {
        for (k, v) in take(&mut self.eqmap) {
            self.eqmap.insert(map(k), v);
        }
        self.vmap.map_key(map);
    }

    #[inline]
    pub fn filter_map_var(&mut self, map: impl Fn(Var) -> Option<Var>) {
        for (k, v) in take(&mut self.eqmap) {
            if let Some(n) = map(k) {
                self.eqmap.insert(n, v);
            }
        }
        self.vmap.filter_map_key(map);
    }

    #[inline]
    pub fn retain(&mut self, f: impl Fn(Var) -> bool) {
        self.vmap.retain(|&k, _| f(k));
        self.eqmap.retain(|&k, _| f(k));
    }

    #[inline]
    pub fn replace(&mut self, x: Var, y: Lit) {
        if let Some(xm) = self.vmap.get(&x) {
            let xm = xm.lit().not_if(!y.polarity());
            self.eqmap.entry(y.var()).or_default().push(xm);
        }
        self.vmap.remove(&x);
    }

    pub fn eq_invariant(&self) -> LitVvec {
        let mut res = LitVvec::new();
        for (v, eq) in self.eqmap.iter() {
            let v = self.restore(v.lit());
            for &e in eq.iter() {
                res.push(LitVec::from([v, !e]));
                res.push(LitVec::from([!v, e]));
            }
        }
        res
    }
}
