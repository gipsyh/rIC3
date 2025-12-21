use crate::cli::{cill::Cill, yosys::Yosys};
use giputils::file::remove_if_exists;
use log::info;
use rIC3::{frontend::Frontend, wltransys::certify::WlWitness};
use serde::{Deserialize, Serialize};
use std::fs;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CtiInfo {
    pub prop: String,
}

impl Cill {
    pub fn save_cti(&mut self, witness: WlWitness) -> anyhow::Result<()> {
        let cti_file = self.rp.path("cill/cti");
        let cti_info_file = self.rp.path("cill/cti.ron");
        let cti_info = CtiInfo {
            prop: self.get_prop_name(witness.bad_id).unwrap(),
        };
        fs::write(cti_info_file, ron::to_string(&cti_info)?)?;
        let witness = self.btorfe.wl_unsafe_certificate(witness);
        fs::write(&cti_file, format!("{}", witness))?;
        let vcd = self.rp.path("cill/cti.vcd");
        Yosys::btor_wit_to_vcd(
            self.rp.path("dut"),
            &cti_file,
            &vcd,
            false,
            self.rcfg.trace.as_ref(),
        )?;
        info!("Witness VCD generated at {}", vcd.display());
        Ok(())
    }

    pub fn clear_cti(&mut self) -> anyhow::Result<()> {
        remove_if_exists(self.rp.path("cill/cti"))?;
        remove_if_exists(self.rp.path("cill/cti.vcd"))?;
        remove_if_exists(self.rp.path("cill/cti.ron"))?;
        Ok(())
    }

    pub fn get_cti_info(&mut self) -> anyhow::Result<CtiInfo> {
        let content = fs::read_to_string(self.rp.path("cill/cti.ron"))?;
        let cti: CtiInfo = ron::from_str(&content)?;
        Ok(cti)
    }
}
