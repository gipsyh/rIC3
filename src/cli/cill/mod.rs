mod cti;
mod tui;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use crate::cli::cill::cti::refresh_cti;
use anyhow::Ok;
use bitwuzla::Bitwuzla;
use btor::Btor;
use clap::Subcommand;
use giputils::{
    file::{create_dir_if_not_exists, recreate_dir, remove_if_exists},
    hash::GHashMap,
    logger::with_log_level,
};
use log::{LevelFilter, info};
use logicrs::{LitVec, VarSymbols, fol::Term};
use rIC3::{
    Engine, McResult,
    frontend::{Frontend, btor::BtorFrontend},
    ic3::{IC3, IC3Config},
    portfolio::{Portfolio, PortfolioConfig},
    transys::Transys,
    wltransys::{bitblast::BitblastRestore, certify::WlWitness, unroll::WlTransysUnroll},
};
use ratatui::crossterm::style::Stylize;
use serde::{Deserialize, Serialize};
use std::{env, fs, thread::spawn};
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
    WaitBlock(String),
    WaitSelect,
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
    ts: Transys,
    _bb_rst: BitblastRestore,
    btorfe: BtorFrontend,
    slv: Bitwuzla,
    uts: WlTransysUnroll,
    symbol: GHashMap<Term, String>,
    res: Vec<bool>,
}

impl CIll {
    pub fn new(rcfg: Ric3Config, rp: Ric3Proj, mut btorfe: BtorFrontend) -> anyhow::Result<Self> {
        create_dir_if_not_exists(rp.path("cill"))?;
        let (mut wts, symbol) = btorfe.wts();
        wts.coi_refine();
        let mut slv = Bitwuzla::new();
        let (ts, bb_rst) = wts.bitblast_to_ts();
        let mut uts = WlTransysUnroll::new(wts);
        uts.unroll_to(3);
        for k in 0..=uts.num_unroll {
            if k != uts.num_unroll {
                for b in uts.ts.bad.iter() {
                    slv.assert(&!uts.next(b, k));
                }
            }
            for c in uts.ts.constraint.iter() {
                slv.assert(&uts.next(c, k));
            }
        }
        Ok(Self {
            rcfg,
            rp,
            btorfe,
            slv,
            ts,
            _bb_rst: bb_rst,
            uts,
            symbol,
            res: Vec::new(),
        })
    }

    fn get_prop_name(&self, id: usize) -> Option<String> {
        self.uts
            .ts
            .bad
            .get(id)
            .and_then(|t| self.symbol.get(t).cloned())
    }

    fn check_inductive(&mut self) -> bool {
        let mut res = vec![false; self.ts.bad.len()];
        let mut cfg = IC3Config::default();
        cfg.time_limit = Some(10);
        cfg.inn = true;
        cfg.preproc.scorr = false;
        cfg.preproc.frts = false;
        with_log_level(LevelFilter::Warn, || {
            let mut joins = Vec::new();
            for i in 0..self.ts.bad.len() {
                let mut ts = self.ts.clone();
                ts.bad = LitVec::from(self.ts.bad[i]);
                for j in 0..self.ts.bad.len() {
                    if i != j {
                        ts.constraint.push(!self.ts.bad[j]);
                    }
                }
                let cfg = cfg.clone();
                joins.push(spawn(move || {
                    let mut ic3 = IC3::new(cfg, ts, VarSymbols::default());
                    ic3.check()
                }));
            }
            for (j, r) in joins.into_iter().zip(res.iter_mut()) {
                *r = matches!(j.join().unwrap(), McResult::Safe);
            }
        });
        for (id, r) in res.iter().enumerate() {
            if *r {
                info!("IC3 proved p{id} is inductive");
            }
        }
        for (i, b) in self.uts.ts.bad.iter().enumerate() {
            if res[i] {
                continue;
            }
            let nb = self.uts.next(b, self.uts.num_unroll);
            res[i] = !self.slv.solve(&[nb]);
        }
        self.res = res;
        self.res.iter().all(|l| *l)
    }

    fn witness(&mut self, id: usize) -> WlWitness {
        let b = &self.uts.ts.bad[id];
        let nb = self.uts.next(b, self.uts.num_unroll);
        assert!(self.slv.solve(&[nb]));
        let mut wit = self.uts.witness(&mut self.slv);
        wit.bad_id = id;
        wit
    }

    fn check_safety(&mut self) -> anyhow::Result<McResult> {
        info!("Starting checking safety for all properties with a 10s time limit.");
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
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .format_target(false)
        .init();

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
    let rcfg = Ric3Config::from_file("ric3.toml")?;
    recreate_dir(rp.path("tmp"))?;
    match rp.check_cached_dut(&rcfg.dut.src())? {
        Some(false) => {
            Yosys::generate_btor(&rcfg, rp.path("tmp/dut"))?;
            refresh_cti(&rp.path("cill/cti"), &rp.path("dut"), &rp.path("tmp/dut"))?;
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

    if let CIllState::WaitBlock(prop) = state {
        if cill.check_cti()? {
            info!("{}", "The CTI has been successfully blocked.".green());
            rp.clear_cti()?;
        } else {
            info!(
                "{}",
                format!("The CTI of {} has NOT been blocked yet.", prop).red()
            );
            return Ok(());
        };
    }

    info!("Checking inductiveness of all properties.");
    if cill.check_inductive() {
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
    rp.set_cill_state(CIllState::WaitSelect)
}

fn select(rp: Ric3Proj, state: CIllState, id: usize) -> anyhow::Result<()> {
    let CIllState::WaitSelect = state else {
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

    let witness = cill.witness(id);
    let name = cill
        .get_prop_name(witness.bad_id)
        .unwrap_or("Unknown".to_string());
    cill.save_cti(witness)?;
    println!(
        "Please analyze the CTI, generate an assertion to block it, and run 'cill check' to confirm the CTI is blocked."
    );
    rp.set_cill_state(CIllState::WaitBlock(name))
}

fn state(_rp: Ric3Proj, state: CIllState) -> anyhow::Result<()> {
    let s = match state {
        CIllState::Check => "waiting to check the inductiveness of assertions",
        CIllState::WaitBlock(p) => &format!("waiting for helper assertions to block CTI of {p}"),
        CIllState::WaitSelect => "waiting to select a non-inductive assertion for CTI generation",
    };
    println!("CIll state: {s}");
    Ok(())
}

fn abort(rp: Ric3Proj, state: CIllState) -> anyhow::Result<()> {
    match state {
        CIllState::Check => {
            println!("Currently in checking state, no abort required.")
        }
        CIllState::WaitBlock(_) => {
            rp.clear_cti()?;
            println!("Successfully aborted the CTI.");
            rp.set_cill_state(CIllState::Check)?;
        }
        CIllState::WaitSelect => {
            println!(
                "Waiting to select a non-inductive assertion for CTI generation, no abort required."
            )
        }
    }
    Ok(())
}
