use crate::cli::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use btor::Btor;
use giputils::{file::recreate_dir, hash::GHashMap};
use logicrs::fol::Term;
use rIC3::frontend::{Frontend, btor::BtorFrontend};
use rIC3::wltransys::{WlTransys, symbol::WlTsSymbol};
use std::{collections::HashMap, path::PathBuf};

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
) -> anyhow::Result<Option<(Term, String)>> {
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
    Ok(Some((target.clone(), format!("{sym} -> {sym}"))))
}

fn make_substitution(
    core_wsym: &WlTsSymbol,
    monitor_wsym: &WlTsSymbol,
) -> anyhow::Result<(GHashMap<Term, Term>, Vec<String>)> {
    let core_symbols = symbols_by_name(core_wsym);
    let mut subst = GHashMap::new();
    let mut notes = Vec::new();
    for (monitor_term, names) in monitor_wsym.signal.iter() {
        for name in names {
            if let Some((replacement, note)) =
                replacement_for_symbol(name, monitor_term, &core_symbols)?
            {
                subst.insert(monitor_term.clone(), replacement);
                notes.push(note);
                break;
            }
        }
    }
    Ok((subst, notes))
}

fn apply_subst(term: &Term, subst: &GHashMap<Term, Term>) -> Term {
    term.apply(|term| subst.get(term).cloned())
}

fn push_symbol(symbols: &mut WlTsSymbol, term: Term, name: String) {
    let names = symbols.signal.entry(term).or_default();
    if !names.contains(&name) {
        names.push(name);
    }
}

fn link_wts(
    mut core_wts: WlTransys,
    mut core_wsym: WlTsSymbol,
    monitor_wts: WlTransys,
    monitor_wsym: WlTsSymbol,
) -> anyhow::Result<(WlTransys, WlTsSymbol, Vec<String>)> {
    let (subst, notes) = make_substitution(&core_wsym, &monitor_wsym)?;

    for input in &monitor_wts.input {
        if !subst.contains_key(input) {
            core_wts.add_input(input);
        }
    }
    for latch in &monitor_wts.latch {
        if !subst.contains_key(latch) {
            let init = monitor_wts
                .init(latch)
                .map(|term| apply_subst(&term, &subst));
            let next = apply_subst(&monitor_wts.next(latch), &subst);
            core_wts.add_latch(latch.clone(), init, next);
        }
    }
    core_wts
        .bad
        .extend(monitor_wts.bad.iter().map(|term| apply_subst(term, &subst)));
    core_wts.constraint.extend(
        monitor_wts
            .constraint
            .iter()
            .map(|term| apply_subst(term, &subst)),
    );
    core_wts.justice.extend(
        monitor_wts
            .justice
            .iter()
            .map(|term| apply_subst(term, &subst)),
    );

    for (term, names) in monitor_wsym.signal {
        let mapped = apply_subst(&term, &subst);
        for name in names {
            push_symbol(&mut core_wsym, mapped.clone(), name);
        }
    }
    core_wsym.prop.extend(monitor_wsym.prop);

    Ok((core_wts, core_wsym, notes))
}

fn link_monitor(
    core_wts: WlTransys,
    core_wsym: WlTsSymbol,
    monitor_wts: WlTransys,
    monitor_wsym: WlTsSymbol,
    linked: PathBuf,
) -> anyhow::Result<()> {
    let (linked_wts, linked_wsym, notes) =
        link_wts(core_wts, core_wsym, monitor_wts, monitor_wsym)?;
    linked_wts.to_btor_with_sym(&linked_wsym).to_file(linked);
    println!("\nLinked signals:");
    for note in notes {
        println!("  {note}");
    }
    Ok(())
}

pub fn link(rcfg: Ric3Config, rp: Ric3Proj) -> anyhow::Result<()> {
    let invariants = rcfg
        .formal
        .as_ref()
        .and_then(|formal| formal.invariants.clone())
        .ok_or_else(|| anyhow::anyhow!("missing required config: formal.invariants"))?;
    let cill_dir = rp.path("cill");
    let shadow = cill_dir.join("shadow.sv");

    let candinv_dir = rp.path("cill/candinv");
    recreate_dir(&candinv_dir)?;
    Yosys::generate_btor_with_files(&rcfg, &[shadow, invariants], &candinv_dir, "invariants")?;

    let mut core_bf = BtorFrontend::new(Btor::from_file(rp.path("wts/wts.btor")));
    let (core_wts, core_wsym) = core_bf.wts();

    let mut candinv_bf = BtorFrontend::new(Btor::from_file(candinv_dir.join("invariants.btor")));
    let (mut candinv_wts, mut candinv_wsym) = candinv_bf.wts();
    candinv_wts.simplify_with_symbols(&mut candinv_wsym);

    link_monitor(
        core_wts,
        core_wsym,
        candinv_wts,
        candinv_wsym,
        candinv_dir.join("linked.btor"),
    )?;
    println!(
        "CIll helper artifacts generated in {}.",
        candinv_dir.display()
    );
    Ok(())
}
