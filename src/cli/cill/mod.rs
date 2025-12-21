mod cti;
mod tui;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use anyhow::Ok;
use bitwuzla::Bitwuzla;
use btor::Btor;
use giputils::{
    file::{recreate_dir, remove_if_exists},
    hash::GHashMap,
    logger::with_log_level,
};
use log::{LevelFilter, info};
use logicrs::{
    LitVec, VarSymbols,
    fol::{BvTermValue, Term, TermValue},
};
use rIC3::{
    Engine, McResult,
    frontend::{Frontend, btor::BtorFrontend},
    ic3::{IC3, IC3Config},
    portfolio::{Portfolio, PortfolioConfig},
    transys::Transys,
    wltransys::{
        WlTransys, bitblast::BitblastRestore, certify::WlWitness, unroll::WlTransysUnroll,
    },
};
use ratatui::crossterm::style::Stylize;
use std::{env, fs, mem::take, path::Path, thread::spawn};

pub struct Cill {
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

impl Cill {
    pub fn new(
        rcfg: Ric3Config,
        rp: Ric3Proj,
        btorfe: BtorFrontend,
        mut wts: WlTransys,
        symbol: GHashMap<Term, String>,
    ) -> Self {
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
        Self {
            rcfg,
            rp,
            btorfe,
            slv,
            ts,
            _bb_rst: bb_rst,
            uts,
            symbol,
            res: Vec::new(),
        }
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
        let mut wit = self.uts.witness(&mut self.slv);
        wit.bad_id = id;
        wit
    }
}

fn refresh_cti(cti_file: &Path, dut_old: &Path, dut_new: &Path) -> anyhow::Result<()> {
    if !cti_file.exists() {
        return Ok(());
    }
    let btor_old = Btor::from_file(dut_old.join("dut.btor"));
    let btorfe_old = BtorFrontend::new(btor_old.clone());
    let mut cti = btorfe_old.deserialize_wl_unsafe_certificate(fs::read_to_string(cti_file)?);
    let ywb_old = btor_old.witness_map(&fs::read_to_string(dut_old.join("dut.ywb"))?);
    let ywb_old_inv: GHashMap<_, _> = ywb_old.into_iter().map(|(k, v)| (v, k)).collect();

    let btor_new = Btor::from_file(dut_new.join("dut.btor"));
    let mut btorfe_new = BtorFrontend::new(btor_new.clone());
    let ywb_new = btor_new.witness_map(&fs::read_to_string(dut_new.join("dut.ywb"))?);

    let mut term_map = GHashMap::new();
    for (n, s) in ywb_new {
        if let Some(o) = ywb_old_inv.get(&s) {
            term_map.insert(o, n);
        }
    }
    for k in 0..cti.len() {
        for x in take(&mut cti.input[k]) {
            if let Some(n) = term_map.get(x.t()) {
                cti.input[k].push(BvTermValue::new(n.clone(), x.v().clone()));
            }
        }
        for x in take(&mut cti.state[k]) {
            if let Some(n) = term_map.get(x.t()) {
                let x = x.try_bv().unwrap();
                cti.state[k].push(TermValue::Bv(BvTermValue::new(n.clone(), x.v().clone())));
            }
        }
    }
    fs::write(
        cti_file,
        format!("{}", btorfe_new.wl_unsafe_certificate(cti)),
    )?;
    Ok(())
}

pub fn cill() -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .format_target(false)
        .init();

    let rcfg = Ric3Config::from_file("ric3.toml")?;
    let rp = Ric3Proj::new()?;
    recreate_dir(rp.path("tmp"))?;
    match rp.check_cached_dut(&rcfg.dut.src())? {
        Some(false) => {
            Yosys::generate_btor(&rcfg, rp.path("tmp/dut"))?;
            refresh_cti(&rp.path("cill/cti"), &rp.path("dut"), &rp.path("tmp/dut"))?;
            fs::remove_dir_all(rp.path("dut"))?;
            fs::rename(rp.path("tmp/dut"), rp.path("dut"))?;
        }
        None => {
            Yosys::generate_btor(&rcfg, rp.path("dut"))?;
            rp.cache_dut(&rcfg.dut.src())?;
        }
        Some(true) => (),
    }
    rp.cache_dut(&rcfg.dut.src())?;
    info!("Starting portfolio engine for all properties with a 10s time limit.");

    let mut cfg = PortfolioConfig::default();
    cfg.config = Some("cill".to_string());
    cfg.time_limit = Some(10);

    let cert_file = rp.path("tmp/dut.cert");

    let btor = Btor::from_file(rp.path("dut/dut.btor"));
    let mut btorfe = BtorFrontend::new(btor.clone());

    let mut engine = Portfolio::new(rp.path("dut/dut.btor"), Some(cert_file.clone()), cfg);
    let res = with_log_level(LevelFilter::Warn, || engine.check());
    let cex_vcd = rp.path("cill/cex.vcd");
    remove_if_exists(&cex_vcd)?;
    match res {
        McResult::Safe => {
            info!("{}", "All properties are SAFE.".green());
            return Ok(());
        }
        McResult::Unsafe(_) => {
            let bid = btorfe
                .deserialize_wl_unsafe_certificate(fs::read_to_string(&cert_file)?)
                .bad_id;
            let bad = btor.bad.get(bid).unwrap();
            let name = btor
                .symbols
                .get(bad)
                .map(|s| s.as_str())
                .unwrap_or("Unknown");
            info!(
                "{}",
                format!("A real counterexample violating {name} was found.").red()
            );
            Yosys::btor_wit_to_vcd(
                rp.path("dut"),
                cert_file,
                &cex_vcd,
                true,
                rcfg.trace.as_ref(),
            )?;
            info!("Counterexample VCD generated at {}", cex_vcd.display());
            return Ok(());
        }
        McResult::Unknown(_) => {
            info!(
                "The portfolio engine failed to obtain a result and will continue with the CILL engine."
            );
        }
    };

    let (wts, symbol) = btorfe.wts();
    fs::create_dir_all(rp.path("cill"))?;
    let cti_file = rp.path("cill/cti");
    let cti = if cti_file.exists() {
        let cti = fs::read_to_string(&cti_file)?;
        Some(btorfe.deserialize_wl_unsafe_certificate(cti))
    } else {
        None
    };

    let mut cill = Cill::new(rcfg, rp, btorfe, wts, symbol);
    if let Some(cti_val) = &cti {
        if cill.check_cti(cti_val) {
            info!("{}", "The CTI has been successfully blocked.".green());
            cill.clear_cti()?;
        } else {
            let cti_info = cill.get_cti_info()?;
            info!(
                "{}",
                format!("The CTI of {} has NOT been blocked yet.", cti_info.prop).red()
            );
            return Ok(());
        }
    }
    info!("Re-checking inductiveness of all properties.");
    if cill.check_inductive() {
        info!(
            "{}",
            "All properties are inductive. Proof succeeded.".green()
        );
        return Ok(());
    }
    let cti = cill.tui_run()?;
    let Some(cti) = cti else {
        return Ok(());
    };
    let witness = cill.witness(cti);
    cill.save_cti(witness)?;
    Ok(())
}
