use crate::wltransys::WlTransys;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{self, BvTermValue, Term, TermValue};
use std::ops::{Deref, DerefMut};

#[derive(Clone, Debug, Default)]
pub struct WlWitness {
    pub input: Vec<Vec<BvTermValue>>,
    pub state: Vec<Vec<TermValue>>,
    pub bad_id: usize,
}

impl WlWitness {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.state.len()
    }

    pub fn resize(&mut self, size: usize) {
        self.input.resize(size, Vec::new());
        self.state.resize(size, Vec::new());
    }

    pub fn enrich(&mut self, observe: &GHashSet<Term>) {
        for k in (0..self.len()).rev() {
            let mut val = GHashMap::new();
            let mut has = GHashSet::new();
            for v in self.input[k].iter() {
                val.insert(v.t().clone(), fol::Value::Bv(v.v().clone()));
                has.insert(v.t().clone());
            }
            for v in self.state[k].iter() {
                val.insert(v.t().clone(), v.v().clone());
                has.insert(v.t().clone());
            }
            for t in observe.iter() {
                if has.contains(t) {
                    continue;
                }
                let val = t.simulate(&mut val);
                if !val.as_bv().unwrap().all_x() {
                    self.state[k].push(TermValue::new(t.clone(), val));
                }
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct WlProof {
    pub proof: WlTransys,
}

impl Deref for WlProof {
    type Target = WlTransys;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.proof
    }
}

impl DerefMut for WlProof {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.proof
    }
}

#[derive(Clone, Default)]
pub struct Restore {
    init_var: Option<Term>,
}

impl Restore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn init_var(&self) -> Option<Term> {
        self.init_var.clone()
    }

    pub fn set_init_var(&mut self, iv: Term) {
        assert!(self.init_var.is_none());
        self.init_var = Some(iv);
    }
}
