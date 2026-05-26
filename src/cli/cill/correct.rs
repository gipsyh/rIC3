use crate::cli::cill::{CIll, utils::CIllStat};
use chrono::TimeDelta;
use giputils::{file::remove_if_exists, logger::with_log_level};
use log::{LevelFilter, info};
use rIC3::{
    BlEngine, Engine, McResult,
    bmc::{BMC, BMCConfig},
};
use ratatui::crossterm::style::Stylize;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::time::Instant;

impl CIll {
    pub fn check_correct(&mut self) -> anyhow::Result<McResult> {
        info!("Checking Correctness");
        let bmc_start = Instant::now();
        let steps = [0, 1, 3, 5, 10, 15];
        let mut results: Vec<(McResult, BMC)> = with_log_level(LevelFilter::Warn, || {
            steps
                .into_par_iter()
                .map(|step| {
                    let mut cfg = BMCConfig::default();
                    cfg.preproc.scorr = false;
                    cfg.preproc.frts = false;
                    if step == 0 {
                        cfg.end = 5;
                    } else {
                        cfg.time_limit = Some(5);
                        cfg.step = step;
                    }
                    let mut bmc = BMC::new(cfg, self.ts.clone());
                    let res = bmc.check();
                    (res, bmc)
                })
                .collect()
        });
        results.retain(|(r, _)| r.is_sat());
        let min_res = results
            .into_iter()
            .min_by_key(|(r, _)| r.into_sat().unwrap());

        let vcd = self.rp.path("cill/cex.vcd");
        remove_if_exists(&vcd)?;

        let mut stat = CIllStat::load(&self.rp)?;
        stat.bmc_time += TimeDelta::from_std(bmc_start.elapsed())?;
        stat.save(&self.rp)?;

        match min_res {
            Some((r, mut bmc)) => {
                let witness = bmc.cex();
                self.save_trace(&witness, false, None, &vcd)?;
                let name = &self.wsym.prop[witness.bad_id];
                println!(
                    "{}",
                    format!(
                        "A CEX violating {name} was found. VCD generated at {}.",
                        vcd.display()
                    )
                    .red()
                );
                Ok(r)
            }
            None => {
                info!("Correctness Checking Passed");
                Ok(McResult::Unknown(None))
            }
        }
    }
}
