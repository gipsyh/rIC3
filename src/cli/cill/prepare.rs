use crate::cli::{
    Ric3Config,
    cill::utils::CIllStat,
    rproj::{PropMcInfo, Ric3Proj},
    verilog::{SvModule, sv_type},
    yosys::Yosys,
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

    rp.save_wts(&wts, &wsym, "wts")?;

    let (mut ts, bbmap) = wts.bitblast_to_ts();
    ts.simplify(&mut Restore::new(&ts));
    rp.save_ts(&ts, Some((&bbmap, "wts")), "ts")?;

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
    cfg.time_limit = Some(if cfg!(debug_assertions) { 3 } else { 30 });
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

fn collect_symbols(root: &mut SvModule, symbols: &BTreeMap<String, Sort>) -> anyhow::Result<()> {
    for (name, sort) in symbols {
        let parts: Vec<_> = name.split('.').map(ToString::to_string).collect();
        let Some((signal_name, path)) = parts.split_last() else {
            continue;
        };
        let children = root.children_entry(path);
        if sort.is_array() {
            children.add_ext_body(format!("{};", sv_type(*sort, signal_name)));
        } else {
            children.add_input(signal_name, *sort);
        }
    }
    Ok(())
}

fn write_shadow(top: &str, symbols: &BTreeMap<String, Sort>, out_dir: &Path) -> anyhow::Result<()> {
    let mut root = SvModule::new(top);
    collect_symbols(&mut root, symbols)?;
    let root_str = format!("{}", root);
    fs::write(out_dir.join("shadow.sv"), root_str)?;
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
