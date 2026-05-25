mod correct;
mod ind;
mod kind;
mod link;
mod prepare;
mod utils;

use super::{Ric3Config, cache::Ric3Proj};
use crate::{
    cli::{cache::DutHash, cill::prepare::cill_prepare},
    logger_init,
};
use anyhow::{Ok, bail};
use btor::Btor;
use clap::Subcommand;
use giputils::{
    file::{create_dir_if_not_exists, remove_if_exists},
    logger::with_log_level,
};
use log::{LevelFilter, info};
use rIC3::{
    McResult,
    frontend::{Frontend, btor::BtorFrontend},
    transys::{Transys, certify::Restore},
    wltransys::{WlTransys, bitblast::BitblastMap, symbol::WlTsSymbol},
};
use ratatui::crossterm::style::Stylize;
use serde::{Deserialize, Serialize};
use std::{env, fs};
use strum::AsRefStr;
use utils::CIllStat;

#[derive(Subcommand, Debug, Clone)]
pub enum CIllCommands {
    /// Prepare shadow DUT artifacts
    Prepare,

    /// Link helper invariants against the prepared DUT
    Link,

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
    pub fn new(rcfg: Ric3Config, rp: Ric3Proj) -> anyhow::Result<Self> {
        let btor = Btor::from_file(rp.path("wts/wts.btor"));
        let mut btorfe = BtorFrontend::new(btor);
        let (wts, wsym) = btorfe.wts();

        // TODO link

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
        CIllCommands::Prepare => prepare::cill_prepare(&rcfg, &rp),
        CIllCommands::Link => link::link(rcfg, rp),
        CIllCommands::Check => check(rcfg, rp, cill_state),
        CIllCommands::Abort => abort(rcfg, rp, cill_state),
        CIllCommands::Select { id } => select(rcfg, rp, cill_state, id),
    }
}

fn check(rcfg: Ric3Config, rp: Ric3Proj, _state: CIllState) -> anyhow::Result<()> {
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
    let select_info = SelectInfo {
        res: cill.res.clone(),
        dh: dut_hash,
    };
    cill.rp.save_serde_obj(&select_info, "cill/select.ron")?;
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
    rp.set_cill_state(CIllState::Check)
}

#[derive(Clone, Deserialize, Serialize)]
struct SelectInfo {
    res: Vec<bool>,
    dh: DutHash,
}

fn select(rcfg: Ric3Config, rp: Ric3Proj, state: CIllState, id: usize) -> anyhow::Result<()> {
    if !rp.path("cill/select.ron").exists() {
        println!("Unable to select: `cill check` has not been run. Please run `cill check`.");
    }
    if let CIllState::Block(p) = state {
        println!("A CTI for {p} already exists. It has been cleared.");
        rp.clear_cti()?;
        rp.set_cill_state(CIllState::Check)?;
    }
    let select_info: SelectInfo = rp.load_serde_obj("cill/select.ron")?;
    if select_info.dh != rcfg.dut.src_hash()? {
        println!("DUT modified, selection cannot proceed. Please re-run the 'check'.");
        rp.set_cill_state(CIllState::Check)?;
        return Ok(());
    }
    let rcfg = Ric3Config::from_file("ric3.toml")?;
    assert!(matches!(
        rp.check_cached_dut(&rcfg.dut.src_hash()?)?,
        Some(true)
    ));
    let mut cill = CIll::new(rcfg, rp.clone())?;
    cill.res = select_info.res;
    if cill.res[id] {
        cill.print_ind_res()?;
        println!(
            "{} is inductive, please select a non-inductive assertion.",
            cill.wsym.prop[id]
        );
        return Ok(());
    }
    let cex = cill.get_cti(id)?;
    cill.save_cex(&cex, rp.path("cill/cti"), Some(rp.path("cill/cti.vcd")))?;
    let name = &cill.wsym.prop[cex.bad_id];
    println!(
        "CTI VCD generated in {}.",
        rp.path("cill/cti.vcd").display()
    );
    rp.set_cill_state(CIllState::Block(name.to_string()))
}

fn abort(_rcfg: Ric3Config, rp: Ric3Proj, state: CIllState) -> anyhow::Result<()> {
    match state {
        CIllState::Check => {
            println!("No CTI exists; abort is not required.");
        }
        CIllState::Block(_) => {
            rp.clear_cti()?;
            println!("Successfully aborted the CTI.");
            rp.set_cill_state(CIllState::Check)?;
        }
    }
    Ok(())
}
