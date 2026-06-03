use crate::wltransys::WlTransys;
use giputils::hash::GHashMap;
use logicrs::fol::{Term, TermSymbol};
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeSet,
    ops::{Deref, DerefMut},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WlTsSymbol {
    pub signal: TermSymbol,
    pub prop: Vec<String>,
}

impl Deref for WlTsSymbol {
    type Target = TermSymbol;

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

    pub fn get_sym2term_map(&self) -> GHashMap<String, Term> {
        self.signal
            .iter()
            .flat_map(|(term, names)| names.iter().map(|name| (name.clone(), term.clone())))
            .collect()
    }
}

fn replacement_for_symbol(
    sym: &str,
    monitor_term: &Term,
    core_symbols: &GHashMap<String, Term>,
) -> anyhow::Result<Option<Term>> {
    let Some(target) = core_symbols.get(sym) else {
        return Ok(None);
    };
    let monitor_sort = monitor_term.sort();
    let target_sort = target.sort();
    if monitor_sort != target_sort {
        anyhow::bail!(
            "symbol type mismatch for {sym}: {:?} and {:?}",
            monitor_sort,
            target_sort
        );
    }
    Ok(Some(target.clone()))
}

fn make_substitution(
    core_wsym: &WlTsSymbol,
    monitor_wsym: &WlTsSymbol,
) -> anyhow::Result<(GHashMap<Term, Term>, Vec<String>)> {
    let core_symbols = core_wsym.get_sym2term_map();
    let mut subst = GHashMap::new();
    let mut unlinked = BTreeSet::new();
    for (monitor_term, names) in monitor_wsym.signal.iter() {
        let mut replacement = None;
        for name in names {
            if let Some(term) = replacement_for_symbol(name, monitor_term, &core_symbols)? {
                replacement = Some(term);
                break;
            }
        }
        if let Some(replacement) = replacement {
            subst.insert(monitor_term.clone(), replacement);
        } else {
            unlinked.extend(names.iter().cloned());
        }
    }
    Ok((subst, unlinked.into_iter().collect()))
}

fn apply_subst(term: &Term, subst: &GHashMap<Term, Term>) -> Term {
    term.apply(&|term| subst.get(term).cloned())
}

pub fn link_wts_by_symbol(
    x_wts: &WlTransys,
    x_wsym: &WlTsSymbol,
    y_wts: WlTransys,
    y_wsym: WlTsSymbol,
) -> anyhow::Result<(WlTransys, WlTsSymbol, Vec<String>)> {
    let (subst, unlinked_symbols) = make_substitution(&x_wsym, &y_wsym)?;
    let mut linked_wts = x_wts.clone();
    let mut linked_wsym = x_wsym.clone();
    for input in &y_wts.input {
        if !subst.contains_key(input) {
            linked_wts.add_input(input);
        }
    }
    for latch in &y_wts.latch {
        if !subst.contains_key(latch) {
            let init = y_wts.init(latch).map(|term| apply_subst(&term, &subst));
            let next = apply_subst(&y_wts.next(latch), &subst);
            linked_wts.add_latch(latch.clone(), init, next);
        }
    }
    linked_wts
        .bad
        .extend(y_wts.bad.iter().map(|term| apply_subst(term, &subst)));
    linked_wts
        .output
        .extend(y_wts.output.iter().map(|term| apply_subst(term, &subst)));
    linked_wts.constraint.extend(
        y_wts
            .constraint
            .iter()
            .map(|term| apply_subst(term, &subst)),
    );

    for (term, names) in y_wsym.signal {
        let mapped = apply_subst(&term, &subst);
        for name in names {
            linked_wsym.add_symbol(&mapped, name);
        }
    }
    linked_wsym.prop.extend(y_wsym.prop);

    Ok((linked_wts, linked_wsym, unlinked_symbols))
}
