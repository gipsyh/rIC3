use crate::cli::{
    VcdConfig,
    cache::Ric3Proj,
    cill::{CIll, CIllState},
    vcd::wlwitness_vcd,
};
use btor::Btor;
use giputils::{file::remove_if_exists, grc::Grc, hash::GHashMap, logger::with_log_level};
use log::LevelFilter;
use logicrs::{
    LitVec, LitVvec, VarSymbols,
    fol::{self, BvTermValue, TermValue},
    satif::Satif,
};
use rIC3::{
    Engine, McResult, McWitness,
    frontend::{Frontend, btor::BtorFrontend},
    gipsat::TransysSolver,
    ic3::{IC3, IC3Config},
    transys::{TransysIf, unroll::TransysUnroll},
    wltransys::certify::WlWitness,
};
use rayon::prelude::*;
use std::{
    fs::{self, File},
    io::BufWriter,
    mem::take,
    path::Path,
};

impl CIll {
    fn save_invariants(&mut self, invariants: &LitVvec) -> anyhow::Result<()> {
        let inv = self.rp.path("cill/inv.ron");
        remove_if_exists(&inv)?;
        fs::write(inv, ron::to_string(&invariants).unwrap())?;
        Ok(())
    }

    fn load_invariants(&mut self) -> anyhow::Result<LitVvec> {
        let inv = self.rp.path("cill/inv.ron");
        let inv: LitVvec = ron::from_str(&fs::read_to_string(&inv)?)?;
        Ok(inv)
    }

    pub fn check_inductive(&mut self) -> anyhow::Result<bool> {
        let mut cfg = IC3Config::default();
        cfg.pred_prop = true;
        cfg.local_proof = true;
        cfg.preproc.preproc = false;
        cfg.time_limit = Some(10);
        cfg.inn = true;
        let mut results: Vec<_> = with_log_level(LevelFilter::Warn, || {
            (0..self.ts.bad.len())
                .into_par_iter()
                .map(|i| {
                    let mut cfg = cfg.clone();
                    cfg.prop = Some(i);
                    let mut ic3 = IC3::new(cfg.clone(), self.ts.clone(), VarSymbols::default());
                    let res = ic3.check();
                    (matches!(res, McResult::Safe), ic3)
                })
                .collect()
        });
        let mut invariants = LitVvec::new();
        for (_, ic3) in results.iter_mut() {
            invariants.extend(ic3.invariant());
        }
        invariants.subsume_simplify();
        let mut uts = TransysUnroll::new(&self.ts);
        uts.unroll();
        let nts = uts.interal_signals();
        let tsctx = Grc::new(nts.ctx());
        let mut slv = TransysSolver::new(&tsctx);
        for i in invariants.iter() {
            slv.add_clause(&!i);
        }
        for b in self.ts.bad.iter() {
            slv.add_clause(&[!b]);
        }
        for i in invariants.iter() {
            assert!(slv.inductive(i, false));
        }
        for i in invariants.iter() {
            self.slv.add_clause(&!i);
        }
        self.save_invariants(&invariants)?;
        for ((r, _), b) in results.iter_mut().zip(self.uts.ts.bad.iter()) {
            if *r {
                continue;
            }
            let bad = self.uts.lit_next(*b, self.uts.num_unroll);
            *r = !self.slv.solve(&[bad]);
            let mut cti = LitVec::new();
            for s in self.ts.latch() {
                if let Some(s) = self.slv.sat_value_lit(s) {
                    cti.push(s);
                }
            }
            assert!(slv.solve(&cti));
        }
        self.res = results.into_iter().map(|(r, _)| r).collect();
        Ok(self.res.iter().all(|l| *l))
    }

    pub fn check_cti(&mut self) -> anyhow::Result<bool> {
        let cti_file = self.rp.path("cill/cti");
        let cti = fs::read_to_string(&cti_file)?;
        let cti = self.btorfe.deserialize_wl_unsafe_certificate(cti);
        assert!(cti.len() == self.uts.num_unroll + 1);
        let cti = self.bb_map.bitblast_witness(&cti);
        let cti = self.ts_rst.forward_witness(&cti);
        let mut assume = vec![
            self.uts
                .lit_next(self.uts.ts.bad[cti.bad_id], self.uts.num_unroll),
        ];
        for k in 0..=self.uts.num_unroll {
            assume.extend(
                self.uts
                    .lits_next(cti.input[k].iter().chain(cti.state[k].iter()), k),
            );
        }
        Ok(!self.slv.solve(&assume))
    }

    pub fn get_cti(&mut self, id: usize) -> anyhow::Result<WlWitness> {
        let invariants = self.load_invariants()?;
        for i in invariants.iter() {
            self.slv.add_clause(&!i);
        }
        let b = self.uts.lit_next(self.uts.ts.bad[id], self.uts.num_unroll);
        assert!(self.slv.solve(&[b]));
        let mut wit = self.uts.witness(&self.slv);
        wit.bad_id = id;
        wit = self.ts_rst.restore_witness(&wit);
        Ok(self.bb_map.restore_witness(&wit))
    }

    pub fn save_cti(&mut self, mut witness: WlWitness) -> anyhow::Result<()> {
        let cti_file = self.rp.path("cill/cti");
        let bwit = self
            .btorfe
            .unsafe_certificate(McWitness::Wl(witness.clone()));
        fs::write(&cti_file, format!("{}", bwit))?;
        let vcd = self.rp.path("cill/cti.vcd");
        let vcd_file = BufWriter::new(File::create(&vcd)?);
        let filter = if let Some(VcdConfig { top: Some(t) }) = &self.rcfg.trace {
            t.as_str()
                .strip_prefix(&self.rcfg.dut.top)
                .map(|s| s.strip_prefix('.').unwrap_or(s))
                .unwrap()
        } else {
            ""
        };
        witness.enrich(&self.wsym.keys().cloned().collect());
        wlwitness_vcd(&witness, &self.wsym, vcd_file, filter)?;
        // crate::cli::yosys::Yosys::btor_wit_to_vcd(
        //     self.rp.path("dut"),
        //     &cti_file,
        //     &vcd,
        //     false,
        //     self.rcfg.trace.as_ref(),
        // )?;
        println!("Witness VCD generated at {}", vcd.display());
        Ok(())
    }
}

impl Ric3Proj {
    pub fn refresh_cti(&self, dut_old: &Path, dut_new: &Path) -> anyhow::Result<()> {
        match self.get_cill_state()? {
            CIllState::Check => {
                self.clear_cti()?;
                return Ok(());
            }
            CIllState::Block(_) => {
                assert!(self.path("cill/cti").exists());
            }
            CIllState::Select(_) => unreachable!(),
        }
        let btor_old = Btor::from_file(dut_old.join("dut.btor"));
        let btorfe_old = BtorFrontend::new(btor_old.clone());
        let mut cti = btorfe_old
            .deserialize_wl_unsafe_certificate(fs::read_to_string(self.path("cill/cti"))?);
        let ywbc_old = fs::read_to_string(dut_old.join("dut.ywb"))?;
        let ywb_old = btor_old.ywb(&ywbc_old);
        let wb_old = btor_old.witness_map(&ywbc_old);
        let wb_old: GHashMap<_, _> = wb_old.into_iter().map(|(k, v)| (v, k)).collect();

        let btor_new = Btor::from_file(dut_new.join("dut.btor"));
        let mut btorfe_new = BtorFrontend::new(btor_new.clone());
        let ywbc_new = fs::read_to_string(dut_new.join("dut.ywb"))?;
        let ywb_new = btor_new.ywb(&ywbc_new);
        let wb_new = btor_new.witness_map(&ywbc_new);

        let Some(bad_id) = ywb_new
            .asserts
            .iter()
            .position(|s| s.eq(&ywb_old.asserts[cti.bad_id]))
        else {
            self.clear_cti()?;
            self.set_cill_state(CIllState::Check)?;
            return Ok(());
        };
        cti.bad_id = bad_id;

        let mut term_map = GHashMap::new();
        for (n, s) in wb_new {
            if let Some(o) = wb_old.get(&s) {
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
                    let x = x.into_bv();
                    cti.state[k].push(TermValue::new(n.clone(), fol::Value::Bv(x.v().clone())));
                }
            }
        }
        fs::write(
            self.path("cill/cti"),
            format!("{}", btorfe_new.unsafe_certificate(McWitness::Wl(cti))),
        )?;
        Ok(())
    }
}
