use crate::cli::cill::{CIll, kind::CIllKind};
use giputils::{file::remove_if_exists, hash::GHashMap};
use logicrs::LitVvec;
use rIC3::{BlEngine, Engine};
use std::fs;

impl CIll {
    pub fn check_effective(&mut self) -> anyhow::Result<()> {
        let cti_dir = self.rp.path("cill/cti");
        if !self.rp.has_cti() {
            return Ok(());
        }

        let mut effect_res = GHashMap::new();
        for entry in fs::read_dir(&cti_dir)? {
            let entry = entry?;
            if !entry.file_type()?.is_file() {
                continue;
            }
            let cti_path = entry.path();
            if !(cti_path.extension().and_then(|ext| ext.to_str()) == Some("cti")) {
                continue;
            }
            let name = cti_path.file_name().unwrap().to_str().unwrap().to_string();

            let cti = fs::read_to_string(&cti_path)?;
            let vcd_path = cti_path.with_extension("vcd");
            remove_if_exists(&cti_path)?;
            remove_if_exists(&vcd_path)?;
            let cti = self.dut_bf.deserialize_wl_unsafe_certificate(cti);
            let cti = self.bb_map.bitblast_cex(&cti);
            let cti = self.ts_rst.forward_cex(&cti);
            // let invariants = self.rp.load_serde_obj("cill/inv.ron")?;
            let invariants = LitVvec::new();
            let mut kind = CIllKind::new(cti.bad_id, self.ts.clone(), invariants, Some(cti));
            let kind_res = kind.check().is_unsat();
            if !kind_res {
                let witness = kind.cex();
                self.save_trace(&witness, true, None, Some(&cti_path), vcd_path)?;
                println!("The CTI for {} has not been blocked, CTI refreshed.", name);
            } else {
                println!("The CTI for {} has been successfully blocked.", name);
            }
            effect_res.insert(name, kind_res);
        }

        Ok(())
    }
}
