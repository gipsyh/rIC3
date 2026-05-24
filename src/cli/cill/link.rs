use crate::cli::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use btor::Btor;
use giputils::{file::recreate_dir, hash::GHashMap};
use logicrs::fol::{Sort, Term};
use rIC3::frontend::{Frontend, btor::BtorFrontend};
use rIC3::wltransys::{WlTransys, symbol::WlTsSymbol};
use serde::Deserialize;
use std::{collections::HashMap, fs, path::PathBuf};

#[derive(Debug, Deserialize)]
struct LinkMap {
    ports: HashMap<String, LinkEntry>,
}

#[derive(Debug, Deserialize)]
struct LinkEntry {
    path: String,
    memory: bool,
    indices: Vec<isize>,
}

fn symbols_by_name(symbols: &WlTsSymbol) -> HashMap<String, Term> {
    symbols
        .signal
        .iter()
        .flat_map(|(term, names)| names.iter().map(|name| (name.clone(), term.clone())))
        .collect()
}

fn build_memory_concat(
    core_symbols: &HashMap<String, Term>,
    prefix: &str,
    target_sort: Sort,
    indices: &[isize],
) -> Option<(Term, usize, usize)> {
    let Sort::Bv(target_width) = target_sort else {
        return None;
    };
    let mut elems = Vec::new();
    for idx in indices {
        elems.push(core_symbols.get(&format!("{prefix}[{idx}]"))?.clone());
    }
    let first = elems.first()?.clone();
    let elem_width = first.bv_len();
    if elems
        .iter()
        .any(|elem| !matches!(elem.sort(), Sort::Bv(width) if width == elem_width))
        || elem_width * elems.len() != target_width
    {
        return None;
    }
    let mut concat = first;
    for elem in elems.into_iter().skip(1) {
        concat = concat.concat(elem);
    }
    Some((concat, indices.len(), elem_width))
}

fn replacement_for_symbol(
    sym: &str,
    monitor_term: &Term,
    link_map: &HashMap<String, LinkEntry>,
    core_symbols: &HashMap<String, Term>,
) -> Option<(Term, String)> {
    let fallback;
    let entry = if let Some(entry) = link_map.get(sym) {
        entry
    } else if core_symbols.contains_key(sym) {
        fallback = LinkEntry {
            path: sym.to_string(),
            memory: false,
            indices: Vec::new(),
        };
        &fallback
    } else {
        return None;
    };

    if let Some(target) = core_symbols.get(&entry.path) {
        return Some((target.clone(), format!("{sym} -> {}", entry.path)));
    }
    if entry.memory
        && let Some((target, depth, elem_width)) = build_memory_concat(
            core_symbols,
            &entry.path,
            monitor_term.sort(),
            &entry.indices,
        )
    {
        return Some((
            target,
            format!(
                "{sym} -> concat core {}[{}:{}] ({depth} x {elem_width}-bit)",
                entry.path,
                entry.indices.first()?,
                entry.indices.last()?
            ),
        ));
    }
    None
}

fn make_substitution(
    core_wsym: &WlTsSymbol,
    monitor_wsym: &WlTsSymbol,
    link_map: &LinkMap,
) -> (GHashMap<Term, Term>, Vec<String>) {
    let core_symbols = symbols_by_name(core_wsym);
    let mut subst = GHashMap::new();
    let mut notes = Vec::new();
    for (monitor_term, names) in monitor_wsym.signal.iter() {
        for name in names {
            if let Some((replacement, note)) =
                replacement_for_symbol(name, monitor_term, &link_map.ports, &core_symbols)
            {
                subst.insert(monitor_term.clone(), replacement);
                notes.push(note);
                break;
            }
        }
    }
    (subst, notes)
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
    link_map: LinkMap,
) -> (WlTransys, WlTsSymbol, Vec<String>) {
    let (subst, notes) = make_substitution(&core_wsym, &monitor_wsym, &link_map);

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

    (core_wts, core_wsym, notes)
}

fn link_monitor(
    core_wts: WlTransys,
    core_wsym: WlTsSymbol,
    monitor_wts: WlTransys,
    monitor_wsym: WlTsSymbol,
    link_map: PathBuf,
    linked: PathBuf,
) -> anyhow::Result<()> {
    let link_map = toml::from_str::<LinkMap>(&fs::read_to_string(link_map)?)?;
    let (linked_wts, linked_wsym, notes) =
        link_wts(core_wts, core_wsym, monitor_wts, monitor_wsym, link_map);
    linked_wts.to_btor_with_sym(&linked_wsym).to_file(linked);
    println!("\nLinked monitor signals:");
    for note in notes {
        println!("  {note}");
    }
    Ok(())
}

pub fn link(rcfg: Ric3Config, rp: Ric3Proj, invariants: PathBuf) -> anyhow::Result<()> {
    if !rcfg.dut.defines.is_empty() {
        anyhow::bail!("`ric3 cill link` does not support dut.defines");
    }
    if !invariants.exists() {
        anyhow::bail!("invariants file not found: {}", invariants.display());
    }
    let dut_dir = rp.path("dut");
    let cill_dir = rp.path("cill");
    let shadow = cill_dir.join("shadow.sv");
    let link_map = cill_dir.join("link_map.toml");
    let core = dut_dir.join("dut.btor");
    for path in [&shadow, &link_map, &core] {
        if !path.exists() {
            anyhow::bail!(
                "missing prepared DUT artifact: {}. Run `ric3 cill prepare` first.",
                path.display()
            );
        }
    }

    let candinv_dir = rp.path("cill/candinv");
    recreate_dir(&candinv_dir)?;
    Yosys::generate_btor_with_files(&rcfg, &[shadow, invariants], &candinv_dir, "monitor")?;

    let mut core_bf = BtorFrontend::new(Btor::from_file(rp.path("dut/dut.btor")));
    let (core_wts, core_wsym) = core_bf.wts();

    let mut cadinv_bf = BtorFrontend::new(Btor::from_file(candinv_dir.join("monitor.btor")));
    let (cadinv_wts, cadinv_wsym) = cadinv_bf.wts();

    link_monitor(
        core_wts,
        core_wsym,
        cadinv_wts,
        cadinv_wsym,
        link_map,
        candinv_dir.join("linked.btor"),
    )?;
    println!(
        "CIll helper artifacts generated in {}.",
        candinv_dir.display()
    );
    Ok(())
}
