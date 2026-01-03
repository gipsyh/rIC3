use crate::cli::{
    cache::Ric3Proj,
    cill::{CIll, CIllState},
};
use btor::Btor;
use giputils::{file::remove_if_exists, hash::GHashMap, logger::with_log_level};
use log::LevelFilter;
use logicrs::{
    LitVvec, VarSymbols,
    fol::{self, BvTermValue, TermValue},
    satif::Satif,
};
use rIC3::{
    Engine, McResult, McWitness,
    frontend::{Frontend, btor::BtorFrontend},
    ic3::{IC3, IC3Config},
    kind::Kind,
    transys::{certify::BlWitness, unroll::TransysUnroll},
};
use rayon::prelude::*;
use std::{
    fs::{self},
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
        self.save_invariants(&invariants)?;
        for ((r, _), b) in results.iter_mut().zip(0..self.ts.bad.len()) {
            if *r {
                continue;
            }
            let mut kind_cfg = self.kind_cfg.clone();
            kind_cfg.prop = Some(b);
            let mut kind = Kind::new(kind_cfg, self.ts.clone());
            for i in invariants.iter() {
                kind.add_local_constraint(&!i);
            }
            *r = kind.check().is_safe();
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

    pub fn get_cti(&mut self, id: usize) -> anyhow::Result<BlWitness> {
        let invariants = self.load_invariants()?;
        let mut kind_cfg = self.kind_cfg.clone();
        kind_cfg.prop = Some(id);
        let mut kind = Kind::new(kind_cfg, self.ts.clone());
        for i in invariants.iter() {
            kind.add_local_constraint(&!i);
        }
        assert!(kind.check().is_unknown());
        let wit = kind.witness().into_bl().unwrap();
        Ok(wit)
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
