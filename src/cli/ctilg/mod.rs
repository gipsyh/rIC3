mod tui;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use bitwuzla::Bitwuzla;
use btor::Btor;
use giputils::hash::GHashMap;
use logicrs::fol::Term;
use rIC3::{
    frontend::{Frontend, btor::BtorFrontend},
    wltransys::{WlTransys, certify::WlWitness, unroll::WlTransysUnroll},
};

pub struct Ctilg {
    pub(super) ric3_proj: Ric3Proj,
    pub(super) slv: Bitwuzla,
    pub(super) uts: WlTransysUnroll,
    pub(super) symbol: GHashMap<Term, String>,
    pub(super) res: Vec<bool>,
}

impl Ctilg {
    pub fn new(ric3_proj: Ric3Proj, wts: WlTransys, symbol: GHashMap<Term, String>) -> Self {
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
            ric3_proj,
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

    fn wl_witness(&mut self) -> WlWitness {
        for b in self.uts.ts.bad.iter().rev() {
            let nb = self.uts.next(b, self.uts.num_unroll);
            if self.slv.solve(&[nb]) {
                return self.uts.witness(&mut self.slv);
            }
        }
        unreachable!()
    }
}

pub fn ctilg() -> anyhow::Result<()> {
    let ric3_cfg = Ric3Config::from_file("ric3.toml")?;
    let mut ric3_proj = Ric3Proj::new()?;
    let cached = ric3_proj.check_cached_dut(&ric3_cfg.dut_src())?;
    if cached.is_none() {
        Yosys::generate_btor(&ric3_cfg, &ric3_proj.dut_path());
        ric3_proj.cache_dut(&ric3_cfg.dut_src())?;
    } else if let Some(false) = cached {
        // let ctilg_dut = ric3_proj.new_dir_entry(ric3_proj.ctilg_path().join("dut"))?;
        // Yosys::generate_btor(&ric3_cfg, &ctilg_dut);
        todo!();
    }
    let btor = Btor::from_file(ric3_proj.dut_path().join("dut.btor"));
    let mut btorfe = BtorFrontend::new(btor);
    let (wts, symbol) = btorfe.wts();
    let mut ctilg = Ctilg::new(ric3_proj, wts, symbol);
    if ctilg.check_inductive() {
        println!("All properties are inductive.")
    } else {
        ctilg.tui_run()?;
    }
    todo!()
}
