use crate::transys::{Transys, TransysIf};
use giputils::hash::GHashMap;
use logicrs::{Lit, LitVec, LitVvec, Var, VarVMap};

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
    vmap: VarVMap,
    eqmap: GHashMap<Var, LitVec>,
    init_var: Option<Var>,
}

impl Restore {
    pub fn new(ts: &Transys) -> Self {
        Self {
            vmap: VarVMap::new_self_map(ts.max_var()),
            eqmap: GHashMap::default(),
            init_var: None,
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
        if let Some(iv) = self.init_var {
            assert!(iv != v);
        }
    }

    #[inline]
    pub fn add_restore(&mut self, v: Var, l: Var) {
        assert!(!self.vmap.contains_key(&v));
        self.vmap.insert(v, l);
    }

    #[inline]
    pub fn map_var(&mut self, map: impl Fn(Var) -> Var) {
        self.init_var = self.init_var.map(&map);
        self.vmap.map_key(map);
    }

    #[inline]
    pub fn filter_map_var(&mut self, map: impl Fn(Var) -> Option<Var>) {
        self.init_var = self.init_var.map(|l| map(l).unwrap());
        self.vmap.filter_map_key(map);
    }

    #[inline]
    pub fn retain(&mut self, f: impl Fn(Var) -> bool) {
        self.vmap.retain(|&k, _| f(k));
        if let Some(iv) = self.init_var {
            assert!(f(iv));
        }
    }

    #[inline]
    pub fn replace(&mut self, x: Var, y: Lit) {
        let xm = self.vmap[x].lit().not_if(!y.polarity());
        let ym = self.vmap[y.var()];
        self.eqmap.entry(ym).or_default().push(xm);
        if let Some(iv) = self.init_var
            && iv == x
        {
            assert!(y.polarity());
            self.init_var = Some(y.var());
        }
    }

    pub fn eq_invariant(&self) -> LitVvec {
        let mut res = LitVvec::new();
        for (v, eq) in self.eqmap.iter() {
            for &e in eq.iter() {
                res.push(LitVec::from([v.lit(), !e]));
                res.push(LitVec::from([!v.lit(), e]));
            }
        }
        res
    }

    pub fn init_var(&self) -> Option<Var> {
        self.init_var
    }

    pub fn set_init_var(&mut self, iv: Var) {
        assert!(self.init_var.is_none());
        self.init_var = Some(iv);
    }
}
