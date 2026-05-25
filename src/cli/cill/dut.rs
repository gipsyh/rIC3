use crate::cli::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use btor::Btor;
use giputils::file::recreate_dir;
use logicrs::fol::Sort;
use rIC3::{
    frontend::{Frontend, btor::BtorFrontend},
    wltransys::{WlTransys, symbol::WlTsSymbol},
};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

#[derive(Clone, Debug, PartialEq, Eq)]
struct ShadowSignal {
    name: String,
    sort: Sort,
}

#[derive(Clone, Debug, Default)]
struct ShadowModule {
    path: Vec<String>,
    signals: BTreeMap<String, ShadowSignal>,
    children: BTreeMap<String, ShadowModule>,
}

pub fn prepare(rcfg: Ric3Config, rp: Ric3Proj) -> anyhow::Result<()> {
    if !rcfg.dut.defines.is_empty() {
        anyhow::bail!("`ric3 cill prepare` does not support dut.defines");
    }
    let dut_dir = rp.path("dut");
    recreate_dir(&dut_dir)?;
    Yosys::generate_btor(&rcfg, &dut_dir)?;
    let cill_dir = rp.path("cill");
    recreate_dir(&cill_dir)?;
    let (wts, wsym) = dut2wts(dut_dir);
    let symbols = collect_symbol_sorts(&wsym)?;
    write_shadow(&rcfg.dut.top, &symbols, &cill_dir)?;

    let btor = wts.to_btor_with_sym(&wsym);
    let wts_dir = rp.path("wts");
    recreate_dir(&wts_dir)?;
    btor.to_file(wts_dir.join("wts.btor"));
    println!(
        "CIll prepare artifacts generated in {}.",
        cill_dir.display()
    );
    Ok(())
}

fn simple_sv_ident(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}

fn sv_ident(name: &str) -> String {
    if simple_sv_ident(name) {
        name.to_string()
    } else {
        format!("\\{name} ")
    }
}

fn sanitize(name: &str) -> String {
    let mut text = String::new();
    let mut prev_underscore = false;
    for c in name.chars() {
        if c.is_ascii_alphanumeric() || c == '_' || c == '$' {
            text.push(c);
            prev_underscore = false;
        } else if !prev_underscore {
            text.push('_');
            prev_underscore = true;
        }
    }
    let text = text.trim_matches('_');
    let mut text = if text.is_empty() {
        "_".to_string()
    } else {
        text.to_string()
    };
    if text
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_digit() || c == '$')
    {
        text.insert(0, '_');
    }
    text
}

fn split_symbol_name(name: &str) -> Vec<String> {
    name.split('.')
        .filter(|part| !part.is_empty())
        .map(ToString::to_string)
        .collect()
}

fn shadow_module_name(top: &str, path: &[String]) -> String {
    if path.is_empty() {
        top.to_string()
    } else {
        let mut parts = vec![sanitize(top)];
        parts.extend(path.iter().map(|part| sanitize(part)));
        format!("__shadow_{}", parts.join("_"))
    }
}

fn packed_type(sort: Sort) -> anyhow::Result<String> {
    match sort {
        Sort::Bv(1) => Ok("logic".to_string()),
        Sort::Bv(width) => Ok(format!("logic [{}:0]", width - 1)),
        Sort::Array(_, elem_width) if elem_width == 1 => Ok("logic".to_string()),
        Sort::Array(_, elem_width) => Ok(format!("logic [{}:0]", elem_width - 1)),
    }
}

fn array_depth(index_width: usize) -> anyhow::Result<usize> {
    1usize
        .checked_shl(index_width.try_into()?)
        .ok_or_else(|| anyhow::anyhow!("array index width {index_width} is too large"))
}

fn signal_decl(signal: &ShadowSignal) -> anyhow::Result<String> {
    let ty = packed_type(signal.sort)?;
    let name = sv_ident(&signal.name);
    match signal.sort {
        Sort::Bv(_) => Ok(format!("input {ty} {name}")),
        Sort::Array(index_width, _) => {
            let depth = array_depth(index_width)?;
            Ok(format!("input {ty} {name} [0:{}]", depth - 1))
        }
    }
}

fn insert_signal(root: &mut ShadowModule, name: &str, sort: Sort) -> anyhow::Result<()> {
    let parts = split_symbol_name(name);
    let Some((signal_name, path)) = parts.split_last() else {
        return Ok(());
    };
    let mut module = root;
    for inst in path {
        module = module
            .children
            .entry(inst.clone())
            .or_insert_with(|| ShadowModule {
                path: module.path.iter().chain([inst]).cloned().collect(),
                ..Default::default()
            });
    }
    let signal = ShadowSignal {
        name: signal_name.clone(),
        sort,
    };
    if let Some(old) = module.signals.get(signal_name) {
        if old != &signal {
            anyhow::bail!("conflicting shadow signal declarations for {name}");
        }
    } else {
        module.signals.insert(signal_name.clone(), signal);
    }
    Ok(())
}

fn collect_symbols(
    root: &mut ShadowModule,
    symbols: &BTreeMap<String, Sort>,
) -> anyhow::Result<()> {
    for (name, sort) in symbols {
        insert_signal(root, name, *sort)?;
    }
    Ok(())
}

fn emit_module(module: &ShadowModule, top: &str, out: &mut String) -> anyhow::Result<()> {
    let module_name = shadow_module_name(top, &module.path);
    out.push_str(&format!("module {}", sv_ident(&module_name)));
    if module.signals.is_empty() {
        out.push_str(";\n");
    } else {
        out.push_str(" (\n");
        let mut decls = Vec::new();
        for signal in module.signals.values() {
            decls.push(format!("    {}", signal_decl(signal)?));
        }
        out.push_str(&decls.join(",\n"));
        out.push_str("\n);\n");
    }

    if !module.children.is_empty() {
        out.push('\n');
        for (inst, child) in &module.children {
            let child_name = shadow_module_name(top, &child.path);
            out.push_str(&format!(
                "    {} {}();\n",
                sv_ident(&child_name),
                sv_ident(inst)
            ));
        }
    }
    out.push_str("endmodule\n\n");

    for child in module.children.values() {
        emit_module(child, top, out)?;
    }
    Ok(())
}

fn write_shadow(top: &str, symbols: &BTreeMap<String, Sort>, out_dir: &Path) -> anyhow::Result<()> {
    let mut root = ShadowModule::default();
    collect_symbols(&mut root, symbols)?;

    let mut shadow = String::from(
        "// Auto-generated by ric3 cill prepare.\n\
         // Shadow signals are exposed as unconnected module inputs.\n\n",
    );
    emit_module(&root, top, &mut shadow)?;
    fs::write(out_dir.join("shadow.sv"), shadow)?;
    Ok(())
}

fn collect_symbol_sorts(sym: &WlTsSymbol) -> anyhow::Result<BTreeMap<String, Sort>> {
    let mut symbols = BTreeMap::new();
    for (term, names) in sym.signal.iter() {
        for name in names {
            if let Some(sort) = symbols.get(name) {
                if sort != &term.sort() {
                    anyhow::bail!("conflicting sorts for shadow symbol {name}");
                }
            } else {
                symbols.insert(name.clone(), term.sort());
            }
        }
    }
    Ok(symbols)
}

pub fn dut2wts(p: PathBuf) -> (WlTransys, WlTsSymbol) {
    let mut btor = BtorFrontend::new(Btor::from_file(p.join("dut.btor")));
    let (mut wts, mut sym) = btor.wts();
    wts.simplify_with_symbols(&mut sym);
    (wts, sym)
}
