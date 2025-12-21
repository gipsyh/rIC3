use crate::cli::{cill::CIll, yosys::Yosys};
use btor::Btor;
use giputils::hash::GHashMap;
use logicrs::fol::{BvTermValue, Term, TermValue};
use rIC3::{
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
        let mut assume = Vec::new();
        for k in 0..self.uts.num_unroll {
            for input in cti.input[k].iter() {
                let kt = self.uts.next(input.t(), k);
                assume.push(kt.teq(Term::bv_const(input.v().clone())));
            }
            for state in cti.state[k].iter() {
                let state = state.try_bv().unwrap();
                let kt = self.uts.next(state.t(), k);
                assume.push(kt.teq(Term::bv_const(state.v().clone())));
            }
        }
        Ok(!self.slv.solve(&assume))
    }

    pub fn save_cti(&mut self, witness: WlWitness) -> anyhow::Result<()> {
        let cti_file = self.rp.path("cill/cti");
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
        println!("Witness VCD generated at {}", vcd.display());
        Ok(())
    }
}

pub fn refresh_cti(cti_file: &Path, dut_old: &Path, dut_new: &Path) -> anyhow::Result<()> {
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
