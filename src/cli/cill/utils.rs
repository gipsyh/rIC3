use crate::cli::{cill::CIll, rproj::Ric3Proj};
use chrono::{DateTime, Duration, Local};
use rIC3::transys::certify::BlCex;
use serde::{Deserialize, Serialize};
use std::{
    fmt,
    fs::{self},
};

impl CIll {
    pub fn save_trace(&mut self, trace: &BlCex) -> anyhow::Result<()> {
        let trace = self.ts_rst.restore_cex(trace);
        let trace = self.bb_map.restore_cex(&trace);
        let name = self.wsym.prop[trace.bad_id].clone();
        let name = name
            .strip_prefix("invariants.")
            .map(|s| s.to_string())
            .unwrap_or(name);
        // trace.enrich(&self.wsym.keys().cloned().collect());
        self.rp.save_trace("cill/linked", &trace, &name)
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
