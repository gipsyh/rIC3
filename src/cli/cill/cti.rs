use crate::cli::{
    cache::Ric3Proj,
    cill::{CIll, CIllState},
    yosys::Yosys,
};
use btor::Btor;
use giputils::hash::GHashMap;
use logicrs::{
    fol::{self, BvTermValue, TermValue},
    satif::Satif,
};
use rIC3::{
    McWitness,
    frontend::{Frontend, btor::BtorFrontend},
    wltransys::certify::WlWitness,
};
use std::{fs, mem::take, path::Path};

impl CIll {
    pub fn check_cti(&mut self) -> anyhow::Result<bool> {
        let cti_file = self.rp.path("cill/cti");
        let cti = fs::read_to_string(&cti_file)?;
        let cti = self.btorfe.deserialize_wl_unsafe_certificate(cti);
        assert!(cti.len() == self.uts.num_unroll + 1);
        let cti = self.bb_map.bitblast_witness(&cti);
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

    pub fn get_cti(&mut self, id: usize) -> WlWitness {
        let b = self.uts.lit_next(self.uts.ts.bad[id], self.uts.num_unroll);
        assert!(self.slv.solve(&[b]));
        let mut wit = self.uts.witness(&self.slv);
        wit.bad_id = id;
        wit = self.ts_rst.restore_witness(&wit);
        self.bb_map.restore_witness(&wit)
    }

    pub fn save_cti(&mut self, witness: WlWitness) -> anyhow::Result<()> {
        let cti_file = self.rp.path("cill/cti");
        let witness = self.btorfe.unsafe_certificate(McWitness::Wl(witness));
        fs::write(&cti_file, format!("{}", witness))?;
        let vcd = self.rp.path("cill/cti.vcd");
        Yosys::btor_wit_to_vcd(
            self.rp.path("dut"),
            &cti_file,
            &vcd,
            false,
            self.rcfg.trace.as_ref(),
        )?;
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
            CIllState::Select => unreachable!(),
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
