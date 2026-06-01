use giputils::hash::GHashMap;
use logicrs::fol::Term;
use std::ops::{Deref, DerefMut};

#[derive(Debug, Clone)]
pub struct WlTsSymbol {
    pub signal: GHashMap<Term, Vec<String>>,
    pub prop: Vec<String>,
}

impl Deref for WlTsSymbol {
    type Target = GHashMap<Term, Vec<String>>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.signal
    }
}

impl DerefMut for WlTsSymbol {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.signal
    }
}

impl WlTsSymbol {
    pub fn prop_index_by_name(&self, name: &str) -> usize {
        self.prop.iter().position(|prop| prop == name).unwrap()
    }

    pub fn get_term_by_name(&self, name: &str) -> Option<Term> {
        for (k, v) in self.signal.iter() {
            if v.iter().any(|s| s == name) {
                return Some(k.clone());
            }
        }
        None
    }
}
