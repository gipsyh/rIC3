use crate::{
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf, unroll::TransysUnroll},
};
use giputils::hash::GHashMap;
use logicrs::{Lit, LitVec, LitVvec, Var, VarVMap, satif::Satif};
use std::ops::{Deref, DerefMut};

#[derive(Clone, Debug, Default)]
pub struct BlWitness {
    pub input: Vec<LitVec>,
    pub state: Vec<LitVec>,
    pub bad_id: usize,
}

impl BlWitness {
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

    pub fn concat(iter: impl IntoIterator<Item = BlWitness>) -> Self {
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

    pub fn exact_state(&mut self, ts: &Transys, init: bool) {
        let mut uts = TransysUnroll::new(ts);
        uts.unroll_to(self.len() - 1);
        let mut solver = cadical::CaDiCaL::new();
        if init {
            ts.load_init(&mut solver);
        }
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

    pub fn lift(&mut self, ts: &Transys, additional_target: Option<impl Fn(usize) -> LitVec>) {
        let mut slv = DagCnfSolver::new(&ts.rel);
        let mut last_target = LitVec::from(ts.bad[self.bad_id]);
        for k in (0..self.len()).rev() {
            let assump: LitVec = self.input[k]
                .iter()
                .chain(self.state[k].iter())
                .copied()
                .collect();
            let mut cls = ts.constraint.clone();
            if let Some(at) = additional_target.as_ref() {
                cls.extend(at(k));
            }
            cls.extend(last_target);
            cls = !cls;
            assert!(!slv.solve_with_constraint(&assump, vec![cls]));
            self.state[k].retain(|l| slv.unsat_has(*l));
            last_target = ts.lits_next(&self.state[k]);
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct BlProof {
    pub proof: Transys,
}

impl Deref for BlProof {
    type Target = Transys;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.proof
    }
}

impl DerefMut for BlProof {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.proof
    }
}

impl BlProof {
    pub fn new(p: Transys) -> Self {
        Self { proof: p }
    }

    pub fn merge(&mut self, other: &Self, ts: &Transys) {
        self.proof.merge(
            &other.proof,
            |v| {
                if v <= ts.max_var() { Some(v) } else { None }
            },
        );
    }
}

#[derive(Debug, Clone)]
pub struct Restore {
    pub(crate) bvmap: VarVMap,
    pub(crate) fvmap: VarVMap,
    eqmap: GHashMap<Var, LitVec>,
    init_var: Option<Var>,
}

impl Restore {
    pub fn new(ts: &Transys) -> Self {
        Self {
            bvmap: VarVMap::new_self_map(ts.max_var()),
            fvmap: VarVMap::new_self_map(ts.max_var()),
            eqmap: GHashMap::default(),
            init_var: None,
        }
    }

    pub fn forward(&self, l: Lit) -> Lit {
        self.fvmap.lit_map(l).unwrap()
    }

    pub fn restore(&self, l: Lit) -> Lit {
        self.bvmap.lit_map(l).unwrap()
    }

    pub fn try_forward(&self, l: Lit) -> Option<Lit> {
        self.fvmap.lit_map(l)
    }

    pub fn try_restore(&self, l: Lit) -> Option<Lit> {
        self.bvmap.lit_map(l)
    }

    pub fn restore_var(&self, v: Var) -> Var {
        self.bvmap[v]
    }

    #[inline]
    pub fn remove(&mut self, v: Var) {
        if let Some(rv) = self.bvmap.remove(&v) {
            self.fvmap.remove(&rv);
        }
        if let Some(iv) = self.init_var
            && iv == v
        {
            self.init_var = None;
        }
    }

    #[inline]
    pub fn add_restore(&mut self, v: Var, l: Var) {
        assert!(!self.bvmap.contains_key(&v));
        self.bvmap.insert(v, l);
        self.fvmap.insert(l, v);
    }

    #[inline]
    pub fn map_var(&mut self, map: &impl Fn(Var) -> Var) {
        self.init_var = self.init_var.map(&map);
        self.bvmap.map_key(map);
        self.fvmap.map_value(map);
    }

    #[inline]
    pub fn filter_map_var(&mut self, map: &impl Fn(Var) -> Option<Var>) {
        self.init_var = self.init_var.map(|l| map(l).unwrap());
        self.bvmap.filter_map_key(map);
        self.fvmap.filter_map_value(map);
    }

    #[inline]
    pub fn retain(&mut self, f: impl Fn(Var) -> bool) {
        self.bvmap.retain(|&k, _| f(k));
        self.fvmap.retain(|_, k| f(*k));
        if let Some(iv) = self.init_var {
            assert!(f(iv));
        }
    }

    #[inline]
    pub fn replace(&mut self, x: Var, y: Lit) {
        let xm = self.bvmap[x].lit().not_if(!y.polarity());
        let ym = self.bvmap[y.var()];
        self.eqmap.entry(ym).or_default().push(xm);
        if let Some(fv) = self.bvmap.remove(&x) {
            self.fvmap.remove(&fv);
        }
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

    pub fn get_init_var(&mut self, ts: &mut Transys) -> Var {
        if let Some(iv) = self.init_var {
            return iv;
        }
        let iv = ts.add_init_var();
        self.init_var = Some(iv);
        iv
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

    pub fn restore_witness(&self, wit: &BlWitness) -> BlWitness {
        let iv = self.init_var();
        let mut wit = wit.filter_map(|l| (iv != Some(l.var())).then(|| self.restore(l)));
        for s in wit.state.iter_mut() {
            *s = self.restore_eq_state(s);
        }
        wit
    }

    pub fn restore_proof(&self, mut proof: BlProof, ts: &Transys) -> BlProof {
        let mut res = ts.clone();
        proof.constraint.clear();
        res.merge(&proof, |v| self.bvmap.get(&v).copied());
        let eqi = self.eq_invariant();
        for cube in eqi {
            res.bad.push(res.rel.new_and(cube));
        }
        BlProof { proof: res }
    }

    pub fn forward_witness(&self, wit: &BlWitness) -> BlWitness {
        assert!(self.eqmap.is_empty());
        let mut res = wit.clone();
        for k in 0..res.len() {
            res.input[k] = res.input[k]
                .iter()
                .filter_map(|l| self.try_forward(*l))
                .collect();
            res.state[k] = res.state[k]
                .iter()
                .filter_map(|l| self.try_forward(*l))
                .collect();
        }
        res
    }
}
