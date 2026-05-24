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
        let entries: Vec<_> = take(&mut self.signal)
            .into_iter()
            .map(|(term, names)| {
                let mapped = transform
                    .get(&term)
                    .cloned()
                    .unwrap_or_else(|| term.clone());
                (term, mapped, names)
            })
            .collect();
        let mut signal = GHashMap::new();
        for unchanged in [true, false] {
            for (term, mapped, names) in entries.iter() {
                if (term == mapped) != unchanged {
                    continue;
                }
                let entry: &mut Vec<String> = signal.entry(mapped.clone()).or_default();
                for name in names {
                    if !entry.contains(&name) {
                        entry.push(name.clone());
                    }
                }
            }
        }
        self.signal = signal;
    }
}
