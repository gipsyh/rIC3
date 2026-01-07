use crate::cli::{
    cache::Ric3Proj,
    cill::{CIll, CIllState, kind::CIllKind},
};
use btor::Btor;
use giputils::{file::remove_if_exists, hash::GHashMap, logger::with_log_level};
use log::{LevelFilter, info};
use logicrs::{
    LitVvec, VarSymbols,
    fol::{self, BvTermValue, TermValue},
};
use rIC3::{
    Engine, McResult, McWitness,
    frontend::{Frontend, btor::BtorFrontend},
    ic3::{IC3, IC3Config},
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
        cfg.time_limit = Some(15);
        cfg.inn = true;
        let ic3_results: Vec<_> = with_log_level(LevelFilter::Warn, || {
            (0..self.ts.bad.len())
                .into_par_iter()
                .map(|i| {
                    let mut cfg = cfg.clone();
                    cfg.prop = Some(i);
                    let mut ic3 = IC3::new(cfg.clone(), self.ts.clone(), VarSymbols::default());
                    let res = ic3.check();
                    let inv = ic3.invariant();
                    (matches!(res, McResult::Safe), inv)
                })
                .collect()
        });
        let mut invariants = LitVvec::new();
        let mut results = Vec::new();
        let mut ic3_proved = Vec::new();
        for (id, (r, inv)) in ic3_results.into_iter().enumerate() {
            if r {
                ic3_proved.push(id);
            }
            results.push(r);
            invariants.extend(inv);
        }
        if !ic3_proved.is_empty() {
            info!("IC3 proved {:?} prop.", ic3_proved);
        }
        invariants.subsume_simplify();
        let mut uts = TransysUnroll::new(&self.ts);
        uts.unroll();
        self.save_invariants(&invariants)?;
        let kind_results: Vec<_> = with_log_level(LevelFilter::Error, || {
            results
                .iter()
                .enumerate()
                .filter(|(_, r)| !**r)
                .map(|(b, _)| b)
                .collect::<Vec<_>>()
                .into_par_iter()
                .map(|b| {
                    let mut kind = CIllKind::new(b, self.ts.clone(), invariants.clone(), None);
                    let r = kind.check().is_safe();
                    (b, r, kind)
                })
                .collect()
        });

        let mut kinds = Vec::new();
        for (b, r, kind) in kind_results {
            results[b] = r;
            kinds.push(kind);
        }
        self.res = results;
        let res = self.res.iter().all(|l| *l);
        // if res {
        // let mut proof = BlProof::new(self.ts.clone());
        // let inv: LitVec = invariants
        //     .iter()
        //     .map(|inv| proof.rel.new_and(inv))
        //     .collect();
        // proof.bad.extend(inv);
        // for (r, mut ic3) in ic3_results {
        //     if r {
        //         let sp = ic3.proof().into_bl().unwrap();
        //         proof.merge(&sp, &self.ts);
        //     }
        // }
        // if !kinds.is_empty() {
        //     let sp = kinds[0].proof().into_bl().unwrap();
        //     proof.merge(&sp, &self.ts);
        // }
        // let proof = self.ts_rst.restore_proof(proof, &self.ots);
        // let cfg = KindConfig::default();
        // let mut kind = Kind::new(cfg, proof.proof.clone());
        // kind.add_tracer(Box::new(LogTracer::new("kind")));

        // let proof = self.bb_map.restore_proof(&self.wts, &proof);
        // let proof = format!("{}", self.btorfe.safe_certificate(rIC3::McProof::Wl(proof)));
        // fs::write(&self.rp.path("cill/cert"), proof)?;
        // assert!(
        //     self.btorfe
        //         .certify(&self.rp.path("dut/dut.btor"), &self.rp.path("cill/cert"))
        // );
        // }
        Ok(res)
    }

    pub fn check_cti(&mut self) -> anyhow::Result<bool> {
        let cti_file = self.rp.path("cill/cti");
        let cti = fs::read_to_string(&cti_file)?;
        let cti = self.btorfe.deserialize_wl_unsafe_certificate(cti);
        let cti = self.bb_map.bitblast_witness(&cti);
        let cti = self.ts_rst.forward_witness(&cti);
        let mut kind = CIllKind::new(cti.bad_id, self.ts.clone(), LitVvec::new(), Some(cti));
        if kind.check().is_safe() {
            return Ok(true);
        }
        self.rp.clear_cti()?;
        let witness = kind.witness().into_bl().unwrap();
        self.save_witness(
            &witness,
            self.rp.path("cill/cti"),
            Some(self.rp.path("cill/cti.vcd")),
        )?;
        Ok(false)
    }

    pub fn get_cti(&mut self, id: usize) -> anyhow::Result<BlWitness> {
        let invariants = self.load_invariants()?;
        let mut kind = CIllKind::new(id, self.ts.clone(), invariants, None);
        assert!(kind.check().is_unknown());
        let wit = kind.witness().into_bl().unwrap();
        Ok(wit)
    }
}

impl Ric3Proj {
    pub fn refresh_cti(&self, dut_old: &Path, dut_new: &Path) -> anyhow::Result<()> {
        let prop = match self.get_cill_state()? {
            CIllState::Check => {
                self.clear_cti()?;
                return Ok(());
            }
            CIllState::Block(prop) => {
                assert!(self.path("cill/cti").exists());
                prop
            }
            CIllState::Select(_) => unreachable!(),
        };
        let btor_old = Btor::from_file(dut_old.join("dut.btor"));
        let btorfe_old = BtorFrontend::new(btor_old.clone());
        let mut cti = btorfe_old
            .deserialize_wl_unsafe_certificate(fs::read_to_string(self.path("cill/cti"))?);
        let ywbc_old = fs::read_to_string(dut_old.join("dut.ywb"))?;
        let ywb_old = btor_old.ywb(&ywbc_old);
        let wb_old = btor_old.witness_map(&ywbc_old);
        let wb_old: GHashMap<_, _> = wb_old
            .into_iter()
            .filter(|(_, v)| v[0].path[0] != "\\_witness_")
            .map(|(k, v)| (v, k))
            .collect();

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
            info!("{prop} not found. CTI has been removed. Please rerun `ric3 cill check`.");
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
