use giputils::hash::GHashMap;
use logicrs::fol::Term;
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
