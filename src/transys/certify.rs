use crate::transys::{Transys, TransysIf, unroll::TransysUnroll};
use giputils::hash::GHashMap;
use logicrs::{Lit, LitVec, LitVvec, Var, VarVMap, satif::Satif};

#[derive(Clone, Debug, Default)]
pub struct Witness {
    pub input: Vec<LitVec>,
    pub state: Vec<LitVec>,
    pub bad_id: usize,
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
        Self {
            input,
            state,
            bad_id: self.bad_id,
        }
    }

    pub fn filter_map_var(&self, f: impl Fn(Var) -> Option<Var>) -> Self {
        let input = self.input.iter().map(|w| w.filter_map_var(&f)).collect();
        let state = self.state.iter().map(|w| w.filter_map_var(&f)).collect();
        Self {
            input,
            state,
            bad_id: self.bad_id,
        }
    }

    pub fn map(&self, f: impl Fn(Lit) -> Lit) -> Self {
        let input = self.input.iter().map(|w| w.map(&f)).collect();
        let state = self.state.iter().map(|w| w.map(&f)).collect();
        Self {
            input,
            state,
            bad_id: self.bad_id,
        }
    }

    pub fn filter_map(&self, f: impl Fn(Lit) -> Option<Lit>) -> Self {
        let input = self.input.iter().map(|w| w.filter_map(&f)).collect();
        let state = self.state.iter().map(|w| w.filter_map(&f)).collect();
        Self {
            input,
            state,
            bad_id: self.bad_id,
        }
    }

    pub fn concat(iter: impl IntoIterator<Item = Witness>) -> Self {
        let mut res = Self::new();
        for witness in iter {
            res.input.extend(witness.input);
            res.state.extend(witness.state);
        }
        res
    }

    pub fn exact_init_state(&mut self, ts: &impl TransysIf) {
        let assump: Vec<_> = self.state[0]
            .iter()
            .chain(self.input[0].iter())
            .copied()
            .collect();
        let mut solver = cadical::CaDiCaL::new();
        ts.load_init(&mut solver);
        ts.load_trans(&mut solver, true);
        assert!(solver.solve(&assump));
        let mut state = LitVec::new();
        for l in ts.latch() {
            state.push(solver.sat_value_lit(l).unwrap());
        }
        let mut input = LitVec::new();
        for i in ts.input() {
            input.push(solver.sat_value_lit(i).unwrap());
        }
        (self.input[0], self.state[0]) = (input, state);
    }

    pub fn exact_state(&mut self, ts: &Transys) {
        let mut uts = TransysUnroll::new(ts);
        uts.unroll_to(self.len() - 1);
        let mut solver = cadical::CaDiCaL::new();
        ts.load_init(&mut solver);
        for k in 0..=uts.num_unroll {
            uts.load_trans(&mut solver, k, true);
            for l in self.state[k]
                .iter()
                .chain(self.input[k].iter())
                .map(|x| uts.lit_next(*x, k))
            {
                solver.add_clause(&[l]);
            }
        }
        assert!(solver.solve(&[]));
        *self = uts.witness(&solver);
        self.bad_id = ts
            .bad
            .iter()
            .position(|&b| {
                solver
                    .sat_value(uts.lit_next(b, uts.num_unroll))
                    .is_some_and(|v| v)
            })
            .unwrap();
    }
}

#[derive(Clone, Debug, Default)]
pub struct Proof {
    pub proof: Transys,
}

#[derive(Debug, Clone)]
pub struct Restore {
    pub(crate) vmap: VarVMap,
    eqmap: GHashMap<Var, LitVec>,
    init_var: Option<Var>,
    custom_cst: LitVec,
}

impl Restore {
    pub fn new(ts: &Transys) -> Self {
        Self {
            vmap: VarVMap::new_self_map(ts.max_var()),
            eqmap: GHashMap::default(),
            init_var: None,
            custom_cst: LitVec::new(),
        }
    }

    pub fn restore(&self, l: Lit) -> Lit {
        self.vmap.lit_map(l).unwrap()
    }

    pub fn try_restore(&self, l: Lit) -> Option<Lit> {
        self.vmap.lit_map(l)
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
        self.vmap.remove(&x);
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

    pub fn restore_eq_state(&self, s: &LitVec) -> LitVec {
        let mut res = s.clone();
        for l in s.iter() {
            if let Some(eq) = self.eqmap.get(&l.var()) {
                for &el in eq.iter() {
                    res.push(el.not_if(!l.polarity()));
                }
            }
        }
        res.sort();
        res.dedup();
        res
    }

    pub fn add_custom_constraint(&mut self, gi: Lit) {
        self.custom_cst.push(gi);
    }
}
