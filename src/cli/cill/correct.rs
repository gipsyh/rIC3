use crate::cli::cill::{CIll, utils::CIllStat};
use chrono::TimeDelta;
use giputils::{file::remove_if_exists, logger::with_log_level};
use log::LevelFilter;
use rIC3::{
    BlEngine, Engine, McResult,
    bmc::{BMC, BMCConfig},
};
use ratatui::crossterm::style::Stylize;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::time::Instant;

impl CIll {
    pub fn check_correct(&mut self) -> anyhow::Result<McResult> {
        println!("Checking Correctness");
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
                        cfg.time_limit = Some(if cfg!(debug_assertions) { 5 } else { 20 });
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

        let trace = self.rp.path("cill/cex.rtrc");
        let term = self.rp.path("cill/term.ron");
        let tsym = self.rp.path("cill/tsym.ron");
        remove_if_exists(&trace)?;
        remove_if_exists(&term)?;
        remove_if_exists(&tsym)?;

        let mut stat = CIllStat::load(&self.rp)?;
        stat.bmc_time += TimeDelta::from_std(bmc_start.elapsed())?;
        stat.save(&self.rp)?;

        match min_res {
            Some((r, mut bmc)) => {
                let trace = bmc.cex();
                self.save_trace(&trace)?;
                let name = self.wsym.prop[trace.bad_id].clone();
                let name = name
                    .strip_prefix("invariants.")
                    .map(|s| s.to_string())
                    .unwrap_or(name);
                println!(
                    "{}",
                    format!(
                        "Found a CEX that violates {name}. Use the trace tools to inspect the waveform.",
                    )
                    .red()
                );
                Ok(r)
            }
            None => {
                println!("Correctness Checking Passed");
                Ok(McResult::Unknown(None))
            }
        }
    }
}
