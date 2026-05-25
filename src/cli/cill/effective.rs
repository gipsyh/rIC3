use crate::cli::{
    cache::Ric3Proj,
    cill::{CIll, CIllState, kind::CIllKind},
};
use btor::Btor;
use giputils::hash::GHashMap;
use log::info;
use logicrs::fol::{self, BvTermValue, TermValue};
use rIC3::{
    BlEngine, Engine, McWlCertificate,
    frontend::{Frontend, btor::BtorFrontend},
    transys::certify::BlCex,
};
use std::{fs, mem::take, path::Path};

impl CIll {
    pub fn check_cti(&mut self) -> anyhow::Result<bool> {
        let cti_file = self.rp.path("cill/cti");
        let cti = fs::read_to_string(&cti_file)?;
        todo!();
        // let cti = self.btorfe.deserialize_wl_unsafe_certificate(cti);
        // let cti = self.bb_map.bitblast_cex(&cti);
        // let cti = self.ts_rst.forward_cex(&cti);
        // let invariants = self.rp.load_serde_obj("cill/inv.ron")?;
        // let mut kind = CIllKind::new(cti.bad_id, self.ts.clone(), invariants, Some(cti));
        // if kind.check().is_unsat() {
        //     return Ok(true);
        // }
        // self.rp.clear_cti()?;
        // let witness = kind.cex();
        // self.save_cex(
        //     &witness,
        //     self.rp.path("cill/cti"),
        //     Some(self.rp.path("cill/cti.vcd")),
        // )?;
        // Ok(false)
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
            info!("{prop} not found. CTI has been removed.");
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
            format!("{}", btorfe_new.wl_certificate(McWlCertificate::SAT(cti))),
        )?;
        Ok(())
    }
}
