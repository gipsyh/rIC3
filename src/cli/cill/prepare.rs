use crate::cli::{
    Ric3Config, cache::PropMcInfo, cache::Ric3Proj, cill::utils::CIllStat, yosys::Yosys,
};
use anyhow::bail;
use btor::Btor;
use giputils::{file::recreate_dir, logger::with_log_level};
use log::{LevelFilter, info};
use logicrs::{
    VarSymbols,
    fol::{Sort, term_gc},
};
use rIC3::{
    Engine,
    frontend::{Frontend, btor::BtorFrontend},
    ic3::{IC3, IC3Config},
    transys::{TransysIf, certify::Restore},
    wltransys::{
        WlTransys,
        symbol::WlTsSymbol,
        transform::{WlTransform, WlTransformStack},
    },
};
use rayon::{
    ThreadPoolBuilder,
    iter::{IntoParallelIterator, ParallelIterator},
};
use std::{collections::BTreeMap, fs, mem::take, path::Path};

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

pub fn cill_prepare(rcfg: &Ric3Config, rp: &Ric3Proj) -> anyhow::Result<()> {
    if !rcfg.dut.defines.is_empty() {
        bail!("CIll does not support dut.defines");
    }
    recreate_dir(rp.path("res"))?;
    let dut_dir = rp.path("dut");
    recreate_dir(&dut_dir)?;
    Yosys::generate_btor_with_files(&rcfg, &rcfg.dut.files, &dut_dir, "dut", true)?;
    let mut btor = BtorFrontend::new(Btor::from_file(dut_dir.join("dut.btor")));
    let (mut wts, mut wsym) = btor.wts();
    preprocess(rcfg, rp, &mut wts, &mut wsym)?;

    let cill_dir = rp.path("cill");
    recreate_dir(&cill_dir)?;
    let symbols = collect_symbol_sorts(&wsym)?;
    write_shadow(&rcfg.dut.top, &symbols, &cill_dir)?;

    let btor = wts.to_btor_with_sym(&wsym);
    let wts_dir = rp.path("wts");
    recreate_dir(&wts_dir)?;
    btor.to_file(wts_dir.join("wts.btor"));
    CIllStat::init(&rp)?;
    Ok(())
}

fn preprocess(
    _rcfg: &Ric3Config,
    rp: &Ric3Proj,
    wts: &mut WlTransys,
    wsym: &mut WlTsSymbol,
) -> anyhow::Result<()> {
    let mut tf = WlTransformStack::new();
    tf.add(wts.coi_refine());
    tf.trans_sym(wsym);
    let mut keep: Vec<_> = wsym.keys().cloned().collect();
    wts.output = keep.clone();
    tf.extend(wts.simplify(&mut keep));
    // let (rst, pol) = rcfg.reset().unwrap();
    // let rst = wsym.get_term_by_name(&rst).unwrap();
    // tf.extend(wts.reset_to_init(&rst, pol).unwrap());
    // tf.extend(wts.simplify());
    tf.trans_sym(wsym);
    let (mut ts, _) = wts.bitblast_to_ts();
    ts.simplify(&mut Restore::new(&ts));
    info!("{}", ts.statistic());
    let mut cfg = IC3Config::default();
    cfg.pred_prop = true;
    cfg.local_proof = true;
    cfg.preproc.preproc = false;
    let num_prop = ts.bad.len();
    cfg.time_limit = Some(30);
    let pool = ThreadPoolBuilder::new().num_threads(16).build()?;
    let ic3_results: Vec<_> = with_log_level(LevelFilter::Warn, || {
        pool.install(|| {
            (0..num_prop)
                .into_par_iter()
                .map(|i| {
                    let mut cfg = cfg.clone();
                    cfg.prop = Some(i);
                    let mut ic3 = IC3::new(cfg.clone(), ts.clone(), VarSymbols::default());
                    ic3.check()
                })
                .collect()
        })
    });
    let bad = take(&mut wts.bad);
    let prop = take(&mut wsym.prop);
    let mut cache = Vec::new();
    for ((bad, name), res) in bad.into_iter().zip(prop).zip(ic3_results) {
        cache.push(PropMcInfo {
            name: name.clone(),
            res,
            config: None,
        });
        if res.is_unknown() {
            wts.bad.push(bad);
            wsym.prop.push(name);
        }
    }
    rp.cache_res(cache)?;
    info!("Preprocess solved {} properties.", num_prop - wts.bad.len());
    let tf = wts.simplify(&mut keep);
    tf.trans_sym(wsym);
    term_gc();
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
    let mut input_decls = Vec::new();
    let mut internal_decls = Vec::new();
    for signal in module.signals.values() {
        match signal.sort {
            Sort::Bv(_) => {
                let ty = packed_type(signal.sort)?;
                let name = sv_ident(&signal.name);
                input_decls.push(format!("    input {ty} {name}"));
            }
            Sort::Array(index_width, _) => {
                let ty = packed_type(signal.sort)?;
                let name = sv_ident(&signal.name);
                let depth = array_depth(index_width)?;
                internal_decls.push(format!("    {ty} {name} [0:{}];", depth - 1));
            }
        }
    }
    if input_decls.is_empty() {
        out.push_str(";\n");
    } else {
        out.push_str(" (\n");
        out.push_str(&input_decls.join(",\n"));
        out.push_str("\n);\n");
    }
    out.push_str(&internal_decls.join("\n"));
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
         // BV shadow signals are exposed as inputs; array shadow signals are internal logic.\n\n",
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
