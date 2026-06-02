mod candinv;
mod correct;
mod effective;
mod inductive;
mod kind;
mod prepare;
mod utils;

use super::{Ric3Config, rproj::Ric3Proj};
use crate::{
    cli::cill::{
        candinv::{link_candinv, synthesis_candinv},
        prepare::cill_prepare,
    },
    logger_init,
};
use anyhow::bail;
use clap::Subcommand;
use giputils::{file::remove_if_exists, logger::with_log_level};
use log::LevelFilter;
use logicrs::fol::{TermManager, set_term_mgr, term_gc, term_mgr};
use rIC3::{
    transys::{Transys, certify::Restore},
    wltransys::{WlTransys, bitblast::BitblastMap, symbol::WlTsSymbol},
};
use ratatui::crossterm::style::Stylize;
use std::{collections::HashSet, env, fs};
use utils::CIllStat;

#[derive(Subcommand, Debug, Clone)]
pub enum CIllCommands {
    /// Check all the properties
    Check,

    /// Abort generated CTI
    Abort,
}

impl Ric3Proj {
    #[allow(unused)]
    fn has_cti(&self) -> bool {
        let Ok(entries) = fs::read_dir(self.path("cill/cti")) else {
            return false;
        };
        entries.filter_map(Result::ok).any(|entry| {
            entry.file_type().is_ok_and(|ty| ty.is_file())
                && entry.path().extension().and_then(|ext| ext.to_str()) == Some("cti")
        })
    }

    fn clear_cti(&self) -> anyhow::Result<()> {
        remove_if_exists(self.path("cill/cti"))?;
        Ok(())
    }

    fn remove_unused_cti(&self, props: &[String]) {
        let props: HashSet<_> = props.iter().cloned().collect();
        let Ok(entries) = fs::read_dir(self.path("cill/cti")) else {
            return;
        };

        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            if path.extension().and_then(|ext| ext.to_str()) != Some("cti") {
                continue;
            }

            let Some(name) = path.file_stem().and_then(|name| name.to_str()) else {
                continue;
            };
            if props.contains(name) {
                continue;
            }

            let _ = fs::remove_file(&path);
            let _ = fs::remove_file(path.with_extension("vcd"));
        }
    }
}

pub struct CIll {
    rp: Ric3Proj,
    #[allow(unused)]
    wts: WlTransys,
    wsym: WlTsSymbol,
    #[allow(unused)]
    ots: Transys,
    ts: Transys,
    bb_map: BitblastMap,
    ts_rst: Restore,
    dut_wts: WlTransys,
    #[allow(unused)]
    dut_wsym: WlTsSymbol,
}

impl CIll {
    pub fn new(rcfg: Ric3Config, rp: Ric3Proj) -> anyhow::Result<Self> {
        term_gc();
        assert!(term_mgr().is_empty());
        let tm: TermManager = rp.load_serde_obj("wts/term.ron")?;
        set_term_mgr(tm);
        term_mgr().enable_id_map();
        let dut_wts: WlTransys = rp.load_serde_obj("wts/wts.ron")?;
        let dut_wsym: WlTsSymbol = rp.load_serde_obj("wts/wsym.ron")?;
        term_mgr().disable_id_map();

        let mut candinv_bf = synthesis_candinv(&rcfg, &rp)?;
        let (wts, wsym) = link_candinv(&dut_wts, &dut_wsym, &mut candinv_bf)?;
        rp.remove_unused_cti(&wsym.prop);
        wts.to_btor_with_sym(&wsym)
            .to_file(rp.path("cill/candinv/linked.btor"));

        let (mut ts, bb_map) = wts.bitblast_to_ts();
        let ots = ts.clone();
        let mut ts_rst = Restore::new(&ts);
        with_log_level(LevelFilter::Warn, || ts.simplify(&mut ts_rst));
        assert!(!ts.has_gate_init());
        Ok(Self {
            rp,
            dut_wts,
            dut_wsym,
            wsym,
            wts,
            ots,
            ts,
            ts_rst,
            bb_map,
        })
    }
}

pub fn cill(cmd: CIllCommands) -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    logger_init();
    let rcfg = Ric3Config::from_file("ric3.toml")?;
    let rp = Ric3Proj::new()?;
    match cmd {
        CIllCommands::Check => check(rcfg, rp),
        CIllCommands::Abort => abort(rcfg, rp),
    }
}

fn check(rcfg: Ric3Config, rp: Ric3Proj) -> anyhow::Result<()> {
    let dut_hash = rcfg.dut.src_hash()?;
    match rp.check_cached_dut(&dut_hash)? {
        Some(false) => {
            bail!("DUT sources changed, CIll does not allow DUT changes");
        }
        None => {
            cill_prepare(&rcfg, &rp)?;
            rp.cache_dut(&dut_hash)?;
        }
        Some(true) => (),
    }

    let mut cill = CIll::new(rcfg, rp.clone())?;

    if !cill.check_correct()?.is_unknown() {
        return Ok(());
    }

    if cill.check_inductive()? {
        let stat = CIllStat::load(&rp)?;
        println!("CIll Statistic: {}", stat);
        println!(
            "{}",
            "All properties are inductive. Proof succeeded.".green()
        );
        return Ok(());
    }

    // cill.check_effective()?;
    Ok(())
}

fn abort(_rcfg: Ric3Config, rp: Ric3Proj) -> anyhow::Result<()> {
    rp.clear_cti()
}
