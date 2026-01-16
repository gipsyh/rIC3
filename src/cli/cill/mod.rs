mod ind;
mod kind;
mod utils;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use crate::logger_init;
use anyhow::Ok;
use btor::Btor;
use clap::Subcommand;
use giputils::{
    file::{create_dir_if_not_exists, recreate_dir, remove_if_exists},
    logger::with_log_level,
};
use log::{LevelFilter, info};
use rIC3::{
    Engine, McResult,
    bmc::{BMC, BMCConfig},
    frontend::{Frontend, btor::BtorFrontend},
    transys::{Transys, certify::Restore},
    wltransys::{WlTransys, bitblast::BitblastMap, symbol::WlTsSymbol},
};
use ratatui::crossterm::style::Stylize;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::{env, fs};
use strum::AsRefStr;

#[derive(Subcommand, Debug, Clone)]
pub enum CIllCommands {
    /// Check all the properties
    Check,

    /// Abort generated CTI
    Abort,

    /// Select porperty that not inductive to generate CTI
    Select { id: usize },
}

#[derive(Serialize, Deserialize, AsRefStr)]
enum CIllState {
    Check,
    Block(String),
    Select(Vec<bool>),
}

impl Ric3Proj {
    fn get_cill_state(&self) -> anyhow::Result<CIllState> {
        let p = self.path("cill/state.ron");
        if p.exists() {
            let state: CIllState = ron::from_str(&fs::read_to_string(p)?)?;
            Ok(state)
        } else {
            Ok(CIllState::Check)
        }
    }

    fn set_cill_state(&self, s: CIllState) -> anyhow::Result<()> {
        let p = self.path("cill/state.ron");
        fs::write(p, ron::to_string(&s)?)?;
        Ok(())
    }

    fn clear_cti(&self) -> anyhow::Result<()> {
        remove_if_exists(self.path("cill/cti"))?;
        remove_if_exists(self.path("cill/cti.vcd"))?;
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
    btorfe: BtorFrontend,
    res: Vec<bool>,
}

impl CIll {
    pub fn new(rcfg: Ric3Config, rp: Ric3Proj, mut btorfe: BtorFrontend) -> anyhow::Result<Self> {
        create_dir_if_not_exists(rp.path("cill"))?;
        let (wts, wsym) = btorfe.wts();
        let (mut ts, bb_map) = wts.bitblast_to_ts();
        let ots = ts.clone();
        let mut ts_rst = Restore::new(&ts);
        with_log_level(LevelFilter::Warn, || ts.simplify(&mut ts_rst));
        ts.remove_gate_init(&mut ts_rst);
        assert!(ts_rst.init_var().is_none());
        Ok(Self {
            rcfg,
            rp,
            btorfe,
            wsym,
            wts,
            ots,
            ts,
            ts_rst,
            bb_map,
            res: Vec::new(),
        })
    }

    fn check_safety(&mut self) -> anyhow::Result<McResult> {
        info!("BMC: Checking correctness of all properties.");
        let steps = [1, 3, 5, 10, 15];
        let mut results: Vec<(McResult, BMC)> = with_log_level(LevelFilter::Warn, || {
            steps
                .into_par_iter()
                .map(|step| {
                    let mut cfg = BMCConfig::default();
                    cfg.time_limit = Some(10);
                    cfg.step = step;
                    cfg.preproc.scorr = false;
                    cfg.preproc.frts = false;
                    let mut bmc = BMC::new(cfg, self.ts.clone());
                    let res = bmc.check();
                    (res, bmc)
                })
                .collect()
        });
        results.retain(|(r, _)| r.is_unsafe());
        let min_res = results
            .into_iter()
            .min_by_key(|(r, _)| r.into_unsafe().unwrap());

        let cex = self.rp.path("cill/cex");
        let cex_vcd = self.rp.path("cill/cex.vcd");
        remove_if_exists(&cex)?;
        remove_if_exists(&cex_vcd)?;

        match min_res {
            Some((r, mut bmc)) => {
                let witness = bmc.witness().into_bl().unwrap();
                self.save_witness(&witness, cex, Some(&cex_vcd))?;
                let name = &self.wsym.prop[witness.bad_id];
                println!(
                    "{}",
                    format!(
                        "A CEX violating {name} was found. VCD generated at {}.",
                        cex_vcd.display()
                    )
                    .red()
                );
                Ok(r)
            }
            None => {
                info!("BMC found no CEX in limited steps.");
                Ok(McResult::Unknown(None))
            }
        }
    }
}

pub fn cill(cmd: CIllCommands) -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    logger_init();
    let rcfg = Ric3Config::from_file("ric3.toml")?;
    let rp = Ric3Proj::new()?;
    let cill_state = rp.get_cill_state()?;
    match cmd {
        CIllCommands::Check => check(rcfg, rp, cill_state),
        CIllCommands::Abort => abort(rcfg, rp, cill_state),
        CIllCommands::Select { id } => select(rcfg, rp, cill_state, id),
    }
}

fn check(rcfg: Ric3Config, rp: Ric3Proj, state: CIllState) -> anyhow::Result<()> {
    if matches!(state, CIllState::Select(_)) {
        rp.set_cill_state(CIllState::Check)?;
    }

    recreate_dir(rp.path("tmp"))?;
    match rp.check_cached_dut(&rcfg.dut.src())? {
        Some(false) => {
            Yosys::generate_btor(&rcfg, rp.path("tmp/dut"))?;
            if !rp.refresh_cti(&rp.path("dut"), &rp.path("tmp/dut"))? {
                fs::remove_dir_all(rp.path("tmp/dut"))?;
                return Ok(());
            }
            fs::remove_dir_all(rp.path("dut"))?;
            fs::rename(rp.path("tmp/dut"), rp.path("dut"))?;
            rp.cache_dut(&rcfg.dut.src())?;
        }
        None => {
            Yosys::generate_btor(&rcfg, rp.path("dut"))?;
            rp.cache_dut(&rcfg.dut.src())?;
        }
        Some(true) => (),
    }

    let btor = Btor::from_file(rp.path("dut/dut.btor"));
    let btorfe = BtorFrontend::new(btor);
    let mut cill = CIll::new(rcfg, rp.clone(), btorfe)?;

    if !matches!(cill.check_safety()?, McResult::Unknown(_)) {
        return Ok(());
    }

    info!("Checking inductiveness of all properties.");
    if cill.check_inductive()? {
        println!(
            "{}",
            "All properties are inductive. Proof succeeded.".green()
        );
        return Ok(());
    }
    cill.print_ind_res()?;
    if let CIllState::Block(prop) = rp.get_cill_state()? {
        if cill.check_cti()? {
            println!("{}", "The CTI has been successfully blocked.".green());
            rp.clear_cti()?;
        } else {
            println!(
                "{}",
                format!(
                    "The CTI of {prop} has not been blocked yet. {} refreshed.",
                    rp.path("cill/cti.vcd").display()
                )
                .red()
            );
            return Ok(());
        }
    }
    println!(
        "Please run 'ric3 cill select <ID>' to select an non-inductive assertion for CTI generation."
    );
    rp.set_cill_state(CIllState::Select(cill.res.clone()))
}

fn select(_rcfg: Ric3Config, rp: Ric3Proj, state: CIllState, id: usize) -> anyhow::Result<()> {
    let res = match state {
        CIllState::Check => {
            println!("Unable to select: `cill check` has not been run. Please run `cill check`.");
            return Ok(());
        }
        CIllState::Block(p) => {
            println!(
                "Unable to select: A CTI for {p} has already been selected. To select a different one, please run `ric3 cill abort` to clear the current, then rerun `cill check`"
            );
            return Ok(());
        }
        CIllState::Select(items) => items,
    };
    let rcfg = Ric3Config::from_file("ric3.toml")?;
    if !matches!(rp.check_cached_dut(&rcfg.dut.src())?, Some(true)) {
        println!("DUT modified, selection cannot proceed. Please re-run the 'check'.");
        rp.set_cill_state(CIllState::Check)?;
        return Ok(());
    }
    let btor = Btor::from_file(rp.path("dut/dut.btor"));
    let btorfe = BtorFrontend::new(btor);
    let mut cill = CIll::new(rcfg, rp.clone(), btorfe)?;
    cill.res = res;
    if cill.res[id] {
        cill.print_ind_res()?;
        println!(
            "{} is inductive, please select a non-inductive assertion.",
            cill.wsym.prop[id]
        );
        return Ok(());
    }
    let witness = cill.get_cti(id)?;
    cill.save_witness(&witness, rp.path("cill/cti"), Some(rp.path("cill/cti.vcd")))?;
    let name = &cill.wsym.prop[witness.bad_id];
    println!(
        "CTI VCD generated in {}.",
        rp.path("cill/cti.vcd").display()
    );
    rp.set_cill_state(CIllState::Block(name.to_string()))
}

fn abort(_rcfg: Ric3Config, rp: Ric3Proj, state: CIllState) -> anyhow::Result<()> {
    match state {
        CIllState::Check => {
            println!("Currently in checking state, no abort required.")
        }
        CIllState::Block(_) => {
            rp.clear_cti()?;
            println!("Successfully aborted the CTI.");
            rp.set_cill_state(CIllState::Check)?;
        }
        CIllState::Select(_) => {
            println!(
                "Waiting to select a non-inductive assertion for CTI generation, no abort required."
            )
        }
    }
    Ok(())
}
