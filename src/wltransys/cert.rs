use crate::wltransys::WlTransys;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{Term, TermValue, Value};
use serde::{Deserialize, Serialize};
use std::ops::{Deref, DerefMut};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct WlCex {
    pub input: Vec<Vec<TermValue>>,
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
            for v in self.input[k].iter().chain(self.state[k].iter()) {
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
                .chain(self.input[t].iter())
                .find(|value| value.t() == term)
                .map(|value| value.v())
            {
                values.push(value.clone());
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
    /// inputs that stand in for the `next` of latches without one
    free_next: GHashSet<Term>,
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

    pub fn add_free_next(&mut self, free: Term) {
        assert!(self.free_next.insert(free));
    }

    pub fn is_free_next(&self, t: &Term) -> bool {
        self.free_next.contains(t)
    }
}
