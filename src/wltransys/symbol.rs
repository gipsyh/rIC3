use giputils::hash::GHashMap;
use logicrs::fol::Term;
use std::mem::take;
use std::ops::Deref;

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

impl WlTsSymbol {
    pub fn transform(&mut self, transform: &GHashMap<Term, Term>) {
        for (k, v) in take(&mut self.signal) {
            if let Some(t) = transform.get(&k) {
                let entry = self.signal.entry(t.clone()).or_default();
                entry.extend(v);
            }
        }
    }
}
