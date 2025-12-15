mod tui;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use anyhow::Ok;
use bitwuzla::Bitwuzla;
use btor::Btor;
use giputils::hash::GHashMap;
use logicrs::fol::Term;
use rIC3::{
    frontend::{Frontend, btor::BtorFrontend},
    wltransys::{WlTransys, certify::WlWitness, unroll::WlTransysUnroll},
};
use std::{fs, path::Path, process::Command};

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

    fn witness(&mut self, id: usize) -> WlWitness {
        let b = &self.uts.ts.bad[id];
        let nb = self.uts.next(b, self.uts.num_unroll);
        assert!(self.slv.solve(&[nb]));
        self.uts.witness(&mut self.slv)
    }

    fn btorvcd(
        &mut self,
        dut: impl AsRef<Path>,
        witness: impl AsRef<Path>,
        vcd: impl AsRef<Path>,
    ) -> anyhow::Result<()> {
        let mut btorvcd = Command::new("btorvcd");
        btorvcd.args(["-c", "--vcd"]);
        btorvcd.arg(vcd.as_ref());
        btorvcd.args(["--hierarchical-symbols", "--info"]);
        btorvcd.arg(dut.as_ref().join("dut.info"));
        btorvcd.arg(dut.as_ref().join("dut.btor"));
        btorvcd.arg(witness.as_ref());
        btorvcd.output()?;
        Ok(())
    }
}

pub fn ctilg() -> anyhow::Result<()> {
    let ric3_cfg = Ric3Config::from_file("ric3.toml")?;
    let ric3_proj = Ric3Proj::new()?;
    let cached = ric3_proj.check_cached_dut(&ric3_cfg.dut.src())?;
    if cached.is_none() {
        Yosys::generate_btor(&ric3_cfg, ric3_proj.dut_path())?;
        ric3_proj.cache_dut(&ric3_cfg.dut.src())?;
    } else if let Some(false) = cached {
        // let ctilg_dut = ric3_proj.new_dir_entry(ric3_proj.ctilg_path().join("dut"))?;
        // Yosys::generate_btor(&ric3_cfg, &ctilg_dut);
        todo!();
    }
    let btor = Btor::from_file(ric3_proj.dut_path().join("dut.btor"));
    let mut btorfe = BtorFrontend::new(btor);
    let (wts, symbol) = btorfe.wts();
    let mut ctilg = Ctilg::new(wts, symbol);
    if ctilg.check_inductive() {
        println!("All properties are inductive. Proof succeeded.");
        return Ok(());
    }
    let cti = ctilg.tui_run()?;
    let Some(cti) = cti else {
        return Ok(());
    };
    let witness = ctilg.witness(cti);
    let witness_file = ric3_proj.ctilg_path().join("cti");
    let witness = btorfe.wl_unsafe_certificate(witness);
    fs::write(&witness_file, format!("{}", witness))?;
    ctilg.btorvcd(
        ric3_proj.dut_path(),
        witness_file,
        ric3_proj.ctilg_path().join("cti.vcd"),
    )?;
    Ok(())
}
