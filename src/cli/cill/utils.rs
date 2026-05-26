use crate::cli::{VcdConfig, cache::Ric3Proj, cill::CIll, vcd::wlwitness_vcd};
use chrono::{DateTime, Duration, Local};
use giputils::hash::GHashSet;
use logicrs::fol::Term;
use rIC3::{McWlCertificate, frontend::Frontend, transys::certify::BlCex};
use serde::{Deserialize, Serialize};
use std::{
    fmt,
    fs::{self, File},
    io::BufWriter,
    path::Path,
};

impl CIll {
    pub fn save_cex(
        &mut self,
        cex: &BlCex,
        p: Option<&Path>,
        vcd: impl AsRef<Path>,
    ) -> anyhow::Result<()> {
        let cex = self.ts_rst.restore_cex(cex);
        let mut cex = self.bb_map.restore_cex(&cex);
        let dut_terms: GHashSet<Term> = self
            .dut_wts
            .input
            .iter()
            .chain(self.dut_wts.latch.iter())
            .cloned()
            .collect();
        cex = cex.filter(|t| dut_terms.contains(t));
        let vcd_file = BufWriter::new(File::create(&vcd)?);
        let filter = if let Some(VcdConfig { top: Some(t) }) = &self.rcfg.trace {
            t.as_str()
                .strip_prefix(&self.rcfg.dut.top)
                .map(|s| s.strip_prefix('.').unwrap_or(s))
                .unwrap()
        } else {
            ""
        };

        cex.enrich(&self.dut_wsym.keys().cloned().collect());
        wlwitness_vcd(&cex, &self.dut_wsym, vcd_file, filter)?;
        if let Some(p) = p {
            let bwit = self
                .dut_bf
                .wl_certificate(McWlCertificate::SAT(cex.clone()));
            fs::write(&p, format!("{}", bwit))?;
        }
        Ok(())
    }
}

#[derive(Serialize, Deserialize)]
pub struct CIllStat {
    pub start: DateTime<Local>,
    pub bmc_time: Duration,
    pub ind_time: Duration,
}

impl Default for CIllStat {
    fn default() -> Self {
        Self {
            start: Local::now(),
            bmc_time: Duration::zero(),
            ind_time: Duration::zero(),
        }
    }
}

impl CIllStat {
    pub fn init(rp: &Ric3Proj) -> anyhow::Result<()> {
        if rp.path("cill/statistic.ron").exists() {
            return Ok(());
        }
        let stat = Self::default();
        stat.save(rp)
    }

    pub fn load(rp: &Ric3Proj) -> anyhow::Result<Self> {
        let content = fs::read_to_string(rp.path("cill/statistic.ron"))?;
        Ok(ron::from_str(&content)?)
    }

    pub fn save(&self, rp: &Ric3Proj) -> anyhow::Result<()> {
        fs::write(rp.path("cill/statistic.ron"), ron::to_string(self)?)?;
        Ok(())
    }
}

impl fmt::Display for CIllStat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let elapsed = Local::now().signed_duration_since(self.start);
        write!(
            f,
            "Total time: {}s, Correctness check: {}s, Inductiveness check: {}s",
            elapsed.num_seconds(),
            self.bmc_time.num_seconds(),
            self.ind_time.num_seconds()
        )
    }
}
