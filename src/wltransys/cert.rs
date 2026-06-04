use crate::wltransys::WlTransys;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{self, BvTermValue, Term, TermValue, Value};
use serde::{Deserialize, Serialize};
use std::ops::{Deref, DerefMut};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct WlCex {
    pub input: Vec<Vec<BvTermValue>>,
    pub state: Vec<Vec<TermValue>>,
    pub bad_id: usize,
}

impl WlCex {
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
                if !val.all_x() {
                    self.state[k].push(TermValue::new(t.clone(), val));
                }
            }
        }
    }

    pub fn filter(&self, f: impl Fn(&Term) -> bool) -> Self {
        Self {
            input: self
                .input
                .iter()
                .map(|frame| frame.iter().filter(|v| f(v.t())).cloned().collect())
                .collect(),
            state: self
                .state
                .iter()
                .map(|frame| frame.iter().filter(|v| f(v.t())).cloned().collect())
                .collect(),
            bad_id: self.bad_id,
        }
    }

    pub fn term_values(&self, term: &Term) -> Vec<Value> {
        let mut values = Vec::new();
        for t in 0..self.len() {
            if let Some(value) = self.state[t]
                .iter()
                .find(|value| value.t() == term)
                .map(|value| value.v())
            {
                values.push(value.clone());
            } else if let Some(value) = self.input[t]
                .iter()
                .find(|value| value.t() == term)
                .map(|value| value.v())
            {
                values.push(Value::Bv(value.clone()));
            } else {
                values.push(Value::default_from(term.sort()));
            }
        }
        values
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
