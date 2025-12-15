mod tui;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use anyhow::Ok;
use bitwuzla::Bitwuzla;
use btor::Btor;
use clap::Parser;
use giputils::{file::recreate_dir, hash::GHashMap};
use log::info;
use logicrs::fol::{Term, TermValue};
use rIC3::{
    config::EngineConfig,
    frontend::{Frontend, btor::BtorFrontend},
    portfolio::Portfolio,
    wltransys::{WlTransys, certify::WlWitness, unroll::WlTransysUnroll},
};
use ratatui::crossterm::style::Stylize;
use std::{env, fs, path::Path, process::Command};

pub struct Ctilg {
    slv: Bitwuzla,
    uts: WlTransysUnroll,
    symbol: GHashMap<Term, String>,
    res: Vec<bool>,
}

impl Ctilg {
    pub fn new(wts: WlTransys, symbol: GHashMap<Term, String>) -> Self {
        let mut slv = Bitwuzla::new();
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
        Self {
            slv,
            uts,
            symbol,
            res: Vec::new(),
        }
    }

    fn check_inductive(&mut self) -> bool {
        let mut res = Vec::new();
        for b in self.uts.ts.bad.iter() {
            let nb = self.uts.next(b, self.uts.num_unroll);
            res.push(!self.slv.solve(&[nb]));
        }
        self.res = res;
        self.res.iter().all(|l| *l)
    }

    fn check_cti(&mut self, cti: &WlWitness) -> bool {
        assert!(cti.len() == self.uts.num_unroll + 1);
        let mut assume = Vec::new();
        for k in 0..self.uts.num_unroll {
            for input in cti.input[k].iter() {
                let kt = self.uts.next(input.t(), k);
                assume.push(kt.teq(Term::bv_const(input.v().clone())));
            }
            for state in cti.state[k].iter() {
                let TermValue::Bv(state) = state else {
                    todo!();
                };
                let kt = self.uts.next(state.t(), k);
                assume.push(kt.teq(Term::bv_const(state.v().clone())));
            }
        }
        !self.slv.solve(&assume)
    }

    fn witness(&mut self, id: usize) -> WlWitness {
        let b = &self.uts.ts.bad[id];
        let nb = self.uts.next(b, self.uts.num_unroll);
        assert!(self.slv.solve(&[nb]));
        self.uts.witness(&mut self.slv)
    }
}

fn btorvcd(
    cex: bool,
    dut: impl AsRef<Path>,
    witness: impl AsRef<Path>,
    vcd: impl AsRef<Path>,
) -> anyhow::Result<()> {
    let mut btorvcd = if cex {
        Command::new("btorsim")
    } else {
        Command::new("btorvcd")
    };
    btorvcd.args(["-c", "--vcd"]);
    btorvcd.arg(vcd.as_ref());
    btorvcd.args(["--hierarchical-symbols", "--info"]);
    btorvcd.arg(dut.as_ref().join("dut.info"));
    btorvcd.arg(dut.as_ref().join("dut.btor"));
    btorvcd.arg(witness.as_ref());
    btorvcd.output()?;
    Ok(())
}

pub fn ctilg() -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .format_target(false)
        .init();
    let ric3_cfg = Ric3Config::from_file("ric3.toml")?;
    let ric3_proj = Ric3Proj::new()?;
    recreate_dir(ric3_proj.path("tmp"))?;
    let cached = ric3_proj.check_cached_dut(&ric3_cfg.dut.src())?;
    if cached.is_none() {
        Yosys::generate_btor(&ric3_cfg, ric3_proj.path("dut"))?;
        ric3_proj.cache_dut(&ric3_cfg.dut.src())?;
    } else if let Some(false) = cached {
        // let ctilg_dut = ric3_proj.new_dir_entry(ric3_proj.ctilg_path().join("dut"))?;
        // Yosys::generate_btor(&ric3_cfg, &ctilg_dut);
        todo!();
    }
    info!("Starting portfolio engine for all properties with a 10s time limit.");
    let cfg = EngineConfig::parse_from(["", "-e", "portfolio", "--time-limit", "10"]);
    let cert_file = ric3_proj.path("tmp/dut.cert");
    let mut engine = Portfolio::new(ric3_proj.path("dut/dut.btor"), Some(cert_file.clone()), cfg);
    let res = engine.check();
    match res {
        Some(true) => {
            info!("{}", "All properties are SAFE.".green());
        }
        Some(false) => {
            info!(
                "{}",
                "A real counterexample was found for property p0.".red()
            );
            let vcd = ric3_proj.path("ctilg/cex.vcd");
            btorvcd(true, ric3_proj.path("dut"), cert_file, &vcd)?;
            info!("Counter example VCD generated at {}", vcd.display());
        }
        None => {
            info!(
                "The portfolio engine failed to obtain a result and will continue with the CTILG engine."
            );
        }
    };

    let btor = Btor::from_file(ric3_proj.path("dut/dut.btor"));
    let mut btorfe = BtorFrontend::new(btor);
    let (wts, symbol) = btorfe.wts();
    fs::create_dir_all(ric3_proj.path("ctilg"))?;
    let cti_file = ric3_proj.path("ctilg/cti");
    let cti = if cti_file.exists() {
        let cti = fs::read_to_string(&cti_file)?;
        Some(btorfe.deserialize_wl_unsafe_certificate(cti))
    } else {
        None
    };

    let mut ctilg = Ctilg::new(wts, symbol);
    if let Some(cti_val) = &cti {
        if ctilg.check_cti(cti_val) {
            info!("{}", "The CTI has been successfully blocked.".green());
            fs::remove_file(cti_file)?;
        } else {
            info!("{}", "The CTI has NOT been blocked yet.".red());
            return Ok(());
        }
    }
    if ctilg.check_inductive() {
        info!(
            "{}",
            "All properties are inductive. Proof succeeded.".green()
        );
        return Ok(());
    }
    let cti = ctilg.tui_run()?;
    let Some(cti) = cti else {
        return Ok(());
    };
    let witness = ctilg.witness(cti);
    let witness_file = ric3_proj.path("ctilg/cti");
    let witness = btorfe.wl_unsafe_certificate(witness);
    fs::write(&witness_file, format!("{}", witness))?;
    btorvcd(
        false,
        ric3_proj.path("dut"),
        witness_file,
        ric3_proj.path("ctilg/cti.vcd"),
    )?;
    info!(
        "Witness VCD generated at {}",
        ric3_proj.path("ctilg/cti.vcd").display()
    );
    Ok(())
}
