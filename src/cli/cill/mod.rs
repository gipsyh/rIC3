mod candinv;
mod correct;
mod effective;
mod inductive;
mod kind;
mod prepare;
mod utils;

use super::{Ric3Config, cache::Ric3Proj};
use crate::{
    cli::{
        cache::DutHash,
        cill::{
            candinv::{link_candinv, synthesis_candinv},
            prepare::cill_prepare,
        },
    },
    logger_init,
};
use anyhow::{Ok, bail};
use btor::Btor;
use clap::Subcommand;
use giputils::{file::remove_if_exists, logger::with_log_level};
use log::LevelFilter;
use rIC3::{
    frontend::{Frontend, btor::BtorFrontend},
    transys::{
        Transys,
        certify::{BlCex, Restore},
    },
    wltransys::{WlTransys, bitblast::BitblastMap, certify::WlCex, symbol::WlTsSymbol},
};
use ratatui::crossterm::style::Stylize;
use std::{env, fs};
use utils::CIllStat;

#[derive(Subcommand, Debug, Clone)]
pub enum CIllCommands {
    /// Check all the properties
    Check,

    /// Abort generated CTI
    Abort,
}

impl Ric3Proj {
    fn has_cti(&self) -> bool {
        self.path("cill/cti").exists()
    }

    fn clear_cti(&self) -> anyhow::Result<()> {
        remove_if_exists(self.path("cill/cti"))?;
        Ok(())
    }
}

pub struct CIll {
    rcfg: Ric3Config,
    rp: Ric3Proj,
    #[allow(unused)]
    wts: WlTransys,
    wsym: WlTsSymbol,
    #[allow(unused)]
    ots: Transys,
    ts: Transys,
    bb_map: BitblastMap,
    ts_rst: Restore,
    dut_bf: BtorFrontend,
}

impl CIll {
    pub fn new(rcfg: Ric3Config, rp: Ric3Proj) -> anyhow::Result<Self> {
        let btor = Btor::from_file(rp.path("wts/wts.btor"));
        let mut dut_bf = BtorFrontend::new(btor);
        let (dut_wts, dut_wsym) = dut_bf.wts();

        let mut candinv_bf = synthesis_candinv(&rcfg, &rp)?;
        let (wts, wsym) = link_candinv(&dut_wts, &dut_wsym, &mut candinv_bf)?;
        wts.to_btor_with_sym(&wsym)
            .to_file(rp.path("cill/candinv/linked.btor"));

        let (mut ts, bb_map) = wts.bitblast_to_ts();
        let ots = ts.clone();
        let mut ts_rst = Restore::new(&ts);
        with_log_level(LevelFilter::Warn, || ts.simplify(&mut ts_rst));
        assert!(!ts.has_gate_init());
        Ok(Self {
            rcfg,
            rp,
            dut_bf,
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

    cill.check_effective()?;
    // if let CIllState::Block(prop) = rp.get_cill_state()? {
    //     if cill.check_cti()? {
    //         println!("{}", "The CTI has been successfully blocked.".green());
    //         rp.clear_cti()?;
    //     } else {
    //         println!(
    //             "{}",
    //             format!(
    //                 "The CTI of {prop} has not been blocked yet. {} refreshed.",
    //                 rp.path("cill/cti.vcd").display()
    //             )
    //             .red()
    //         );
    //         return Ok(());
    //     }
    // }
    println!(
        "Please run 'ric3 cill select <ID>' to select an non-inductive assertion for CTI generation."
    );
    Ok(())
}

fn abort(_rcfg: Ric3Config, rp: Ric3Proj) -> anyhow::Result<()> {
    // match state {
    //     CIllState::Check => {
    //         println!("No CTI exists; abort is not required.");
    //     }
    //     CIllState::Block(_) => {
    //         rp.clear_cti()?;
    //         println!("Successfully aborted the CTI.");
    //         rp.set_cill_state(CIllState::Check)?;
    //     }
    // }
    Ok(())
}
