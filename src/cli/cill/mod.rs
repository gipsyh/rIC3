mod ind;
mod tui;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use crate::logger_init;
use anyhow::Ok;
use btor::Btor;
use cadical::CaDiCaL;
use clap::Subcommand;
use giputils::{
    file::{create_dir_if_not_exists, recreate_dir, remove_if_exists},
    hash::GHashMap,
    logger::with_log_level,
};
use log::{LevelFilter, info};
use logicrs::{fol::Term, satif::Satif};
use rIC3::{
    McResult,
    frontend::{Frontend, btor::BtorFrontend},
    portfolio::{Portfolio, PortfolioConfig},
    transys::{Transys, certify::Restore, unroll::TransysUnroll},
    wltransys::{WlTransys, bitblast::BitblastMap},
};
use ratatui::crossterm::style::Stylize;
use serde::{Deserialize, Serialize};
use std::{env, fs};
use strum::AsRefStr;

#[derive(Subcommand, Debug, Clone)]
pub enum CIllCommands {
    /// Query CIll State
    State,

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
    wts: WlTransys,
    wsym: GHashMap<Term, Vec<String>>,
    #[allow(unused)]
    ots: Transys,
    ts: Transys,
    bb_map: BitblastMap,
    ts_rst: Restore,
    btorfe: BtorFrontend,
    slv: CaDiCaL,
    uts: TransysUnroll<Transys>,
    res: Vec<bool>,
}

impl CIll {
    pub fn new(rcfg: Ric3Config, rp: Ric3Proj, mut btorfe: BtorFrontend) -> anyhow::Result<Self> {
        create_dir_if_not_exists(rp.path("cill"))?;
        let (wts, wsym) = btorfe.wts();
        let (mut ts, bb_map) = wts.bitblast_to_ts();
        let ots = ts.clone();
        let mut slv = CaDiCaL::new();
        let mut ts_rst = Restore::new(&ts);
        ts.simplify(&mut ts_rst);
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll_to(4);
        for k in 0..=uts.num_unroll {
            uts.load_trans(&mut slv, k, true);
        }
        for k in 0..uts.num_unroll {
            for b in uts.ts.bad.iter() {
                slv.add_clause(&[!uts.lit_next(*b, k)]);
            }
        }
        Ok(Self {
            rcfg,
            rp,
            btorfe,
            wsym,
            slv,
            wts,
            ots,
            ts,
            ts_rst,
            bb_map,
            uts,
            res: Vec::new(),
        })
    }

    fn get_prop_name(&self, id: usize) -> Option<String> {
        self.wsym.get(&self.wts.bad[id]).map(|l| l[0].clone())
    }

    fn check_safety(&mut self) -> anyhow::Result<McResult> {
        info!("Starting checking safety for all properties.");
        let mut cfg = PortfolioConfig::default();
        cfg.config = Some("cill".to_string());
        cfg.time_limit = Some(10);
        let cert_file = self.rp.path("tmp/dut.cert");
        let mut engine = Portfolio::new(self.rp.path("dut/dut.btor"), Some(cert_file.clone()), cfg);
        let res = with_log_level(LevelFilter::Warn, || engine.check());

        let cex_vcd = self.rp.path("cill/cex.vcd");
        remove_if_exists(&cex_vcd)?;

        match res {
            McResult::Safe => {
                info!("{}", "All properties are SAFE.".green());
            }
            McResult::Unsafe(_) => {
                let bid = self
                    .btorfe
                    .deserialize_wl_unsafe_certificate(fs::read_to_string(&cert_file)?)
                    .bad_id;
                let name = self.get_prop_name(bid).unwrap_or("Unknown".to_string());
                Yosys::btor_wit_to_vcd(
                    self.rp.path("dut"),
                    cert_file,
                    &cex_vcd,
                    true,
                    self.rcfg.trace.as_ref(),
                )?;
                println!(
                    "{}",
                    format!(
                        "A real counterexample violating {name} was found. VCD generated at {}. Please adjust {name} based on the VCD.",
                        cex_vcd.display()
                    )
                    .red()
                );
            }
            McResult::Unknown(_) => {
                info!(
                    "The portfolio engine failed to obtain a result and will continue with the CIll engine."
                );
            }
        };
        Ok(res)
    }
}

pub fn cill(cmd: CIllCommands) -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    logger_init();

    let rp = Ric3Proj::new()?;
    let cill_state = rp.get_cill_state()?;
    match cmd {
        CIllCommands::State => state(rp, cill_state),
        CIllCommands::Check => check(rp, cill_state),
        CIllCommands::Abort => abort(rp, cill_state),
        CIllCommands::Select { id } => select(rp, cill_state, id),
    }
}

fn check(rp: Ric3Proj, state: CIllState) -> anyhow::Result<()> {
    if matches!(state, CIllState::Select(_)) {
        rp.set_cill_state(CIllState::Check)?;
    }
    let rcfg = Ric3Config::from_file("ric3.toml")?;
    recreate_dir(rp.path("tmp"))?;
    match rp.check_cached_dut(&rcfg.dut.src())? {
        Some(false) => {
            Yosys::generate_btor(&rcfg, rp.path("tmp/dut"))?;
            rp.refresh_cti(&rp.path("dut"), &rp.path("tmp/dut"))?;
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

    if let CIllState::Block(prop) = rp.get_cill_state()? {
        if cill.check_cti()? {
            println!("{}", "The CTI has been successfully blocked.".green());
            rp.clear_cti()?;
        } else {
            println!(
                "{}",
                format!("The CTI of {prop} has not been blocked yet.").red()
            );
            return Ok(());
        }
    }

    info!("Checking inductiveness of all properties.");
    if cill.check_inductive()? {
        info!(
            "{}",
            "All properties are inductive. Proof succeeded.".green()
        );
        return Ok(());
    }
    cill.print_ind_res()?;
    println!(
        "Please run 'ric3 cill select <ID>' to select an non-inductive assertion for CTI generation."
    );
    rp.set_cill_state(CIllState::Select(cill.res.clone()))
}

fn select(rp: Ric3Proj, state: CIllState, id: usize) -> anyhow::Result<()> {
    let CIllState::Select(res) = state else {
        println!("No need to select a non-inductive assertion for CTI generation.");
        return Ok(());
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
            cill.get_prop_name(id).unwrap()
        );
        return Ok(());
    }
    let witness = cill.get_cti(id)?;
    let name = cill
        .get_prop_name(witness.bad_id)
        .unwrap_or("Unknown".to_string());
    cill.save_cti(witness)?;
    println!(
        "Please analyze the CTI, generate an assertion to block it, and run 'cill check' to confirm the CTI is blocked."
    );
    rp.set_cill_state(CIllState::Block(name))
}

fn state(_rp: Ric3Proj, state: CIllState) -> anyhow::Result<()> {
    let s = match state {
        CIllState::Check => "waiting to check the inductiveness of assertions",
        CIllState::Block(p) => &format!("waiting for helper assertions to block CTI of {p}"),
        CIllState::Select(_) => "waiting to select a non-inductive assertion for CTI generation",
    };
    println!("CIll state: {s}");
    Ok(())
}

fn abort(rp: Ric3Proj, state: CIllState) -> anyhow::Result<()> {
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
