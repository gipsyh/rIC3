use crate::cli::{Ric3Config, rproj::Ric3Proj, yosys::Yosys};
use btor::Btor;
use giputils::{file::recreate_dir, hash::GHashMap};
use logicrs::fol::Term;
use rIC3::frontend::{Frontend, btor::BtorFrontend};
use rIC3::wltransys::transform::WlTransform;
use rIC3::wltransys::{WlTransys, symbol::WlTsSymbol};
use std::collections::{BTreeSet, HashMap};

fn symbols_by_name(symbols: &WlTsSymbol) -> HashMap<String, Term> {
    symbols
        .signal
        .iter()
        .flat_map(|(term, names)| names.iter().map(|name| (name.clone(), term.clone())))
        .collect()
}

fn replacement_for_symbol(
    sym: &str,
    monitor_term: &Term,
    core_symbols: &HashMap<String, Term>,
) -> anyhow::Result<Option<Term>> {
    let Some(target) = core_symbols.get(sym) else {
        return Ok(None);
    };
    let monitor_sort = monitor_term.sort();
    let target_sort = target.sort();
    if monitor_sort != target_sort {
        anyhow::bail!(
            "shadow symbol type mismatch for {sym}: invariants {:?}, DUT {:?}",
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
    let core_symbols = symbols_by_name(core_wsym);
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

fn push_symbol(symbols: &mut WlTsSymbol, term: Term, name: String) {
    let names = symbols.signal.entry(term).or_default();
    if !names.contains(&name) {
        names.push(name);
    }
}

fn link_wts(
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
            push_symbol(&mut linked_wsym, mapped.clone(), name);
        }
    }
    linked_wsym.prop.extend(y_wsym.prop);

    Ok((linked_wts, linked_wsym, unlinked_symbols))
}

pub fn link_candinv(
    core_wts: &WlTransys,
    core_wsym: &WlTsSymbol,
    candinv_bf: &mut BtorFrontend,
) -> anyhow::Result<(WlTransys, WlTsSymbol)> {
    let (mut candinv_wts, mut candinv_wsym) = candinv_bf.wts();
    let candinv_tf = candinv_wts.simplify(&mut vec![]);
    candinv_tf.trans_sym(&mut candinv_wsym);

    let (linked_wts, linked_wsym, mut unlinked_symbols) =
        link_wts(core_wts, core_wsym, candinv_wts, candinv_wsym)?;
    unlinked_symbols.retain(|s| !s.starts_with("invariants."));
    if !unlinked_symbols.is_empty() {
        println!("Unlinked candinv signals: {}", unlinked_symbols.join(","));
    }
    Ok((linked_wts, linked_wsym))
}

pub fn synthesis_candinv(rcfg: &Ric3Config, rp: &Ric3Proj) -> anyhow::Result<BtorFrontend> {
    let candinv = rcfg
        .formal
        .as_ref()
        .and_then(|formal| formal.invariants.clone())
        .ok_or_else(|| anyhow::anyhow!("missing required config: formal.invariants"))?;
    let shadow = rp.path("cill/shadow.sv");

    let candinv_dir = rp.path("cill/candinv");
    recreate_dir(&candinv_dir)?;
    Yosys::generate_btor_with_files(&rcfg, &[shadow, candinv], &candinv_dir, "invariants", true)?;
    Ok(BtorFrontend::new(Btor::from_file(
        candinv_dir.join("invariants.btor"),
    )))
}
