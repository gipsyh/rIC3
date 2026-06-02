use crate::cli::cill::{CIll, kind::CIllKind, utils::CIllStat};
use chrono::TimeDelta;
use giputils::{file::recreate_dir, logger::with_log_level};
use log::LevelFilter;
use logicrs::{LitVvec, VarSymbols};
use rIC3::{
    BlEngine, Engine, McResult,
    ic3::{IC3, IC3Config},
    transys::{certify::BlCex, unroll::TransysUnroll},
};
use ratatui::crossterm::style::Stylize;
use rayon::{ThreadPoolBuilder, prelude::*};
use std::time::Instant;
use tabled::{
    Table, Tabled,
    settings::{Format, Modify, Style, object::Rows},
};

impl CIll {
    pub fn check_inductive(&mut self) -> anyhow::Result<bool> {
        println!("Checking Inductiveness");
        let ind_start = Instant::now();
        let mut cfg = IC3Config::default();
        cfg.pred_prop = true;
        cfg.preproc.preproc = false;
        cfg.preproc.bve = false;
        cfg.preproc.scorr = false;
        cfg.preproc.frts = false;
        let num_prop = self.ts.bad.len();
        // cfg.time_limit = Some(60 + 6 * self.ts.bad.len() as u64);
        cfg.time_limit = Some(30);
        let pool = ThreadPoolBuilder::new().num_threads(16).build()?;
        let ic3_results: Vec<_> = with_log_level(LevelFilter::Warn, || {
            pool.install(|| {
                (0..num_prop)
                    .into_par_iter()
                    .map(|i| {
                        let ic3res: Vec<_> = [true, false]
                            .into_par_iter()
                            .map(|lp| {
                                let mut cfg = cfg.clone();
                                cfg.local_proof = lp;
                                cfg.inn = !lp;
                                cfg.pred_prop = lp;
                                cfg.preproc.preproc = !lp;
                                cfg.prop = Some(i);
                                let mut ic3 =
                                    IC3::new(cfg.clone(), self.ts.clone(), VarSymbols::default());
                                let res = ic3.check();
                                let inv = ic3.invariant();
                                (matches!(res, McResult::UNSAT), inv, lp as u32 + 1)
                            })
                            .collect();
                        let [(sr, mut si, se), (ir, ii, ie)] = ic3res.try_into().unwrap();
                        si.extend(ii);
                        (sr || ir, si, se + ie)
                        // let [(sr, si, se)] = ic3res.try_into().unwrap();
                        // (sr, si, se)
                    })
                    .collect()
            })
        });
        let mut invariants = LitVvec::new();
        let mut results = Vec::new();
        let mut ic3_proved = Vec::new();
        let mut engines = vec![None; num_prop];
        for (id, (r, inv, lp)) in ic3_results.into_iter().enumerate() {
            if r {
                ic3_proved.push(id);
                engines[id] = Some(format!("IC3({lp})"));
            }
            results.push(r);
            invariants.extend(inv);
        }
        invariants.subsume_simplify();
        let mut uts = TransysUnroll::new(&self.ts);
        uts.unroll();
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
                    let mut cex = None;
                    if !kind.check().is_unsat() {
                        cex = Some(kind.cex());
                    }
                    (b, cex, kind)
                })
                .collect()
        });

        let mut kinds = Vec::new();
        let mut results = vec![None; num_prop];
        for (b, r, kind) in kind_results {
            if r.is_none() {
                engines[b] = Some("K-Ind".to_string())
            }
            results[b] = r;
            kinds.push(kind);
        }
        let res = results.iter().all(|l| l.is_none());

        let mut stat = CIllStat::load(&self.rp)?;
        stat.ind_time += TimeDelta::from_std(ind_start.elapsed())?;
        stat.save(&self.rp)?;

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
        self.print_and_save_res(results, engines)?;
        Ok(res)
    }

    fn print_and_save_res(
        &mut self,
        res: Vec<Option<BlCex>>,
        engines: Vec<Option<String>>,
    ) -> anyhow::Result<()> {
        #[derive(Tabled)]
        struct InductiveResult {
            #[tabled(rename = "Property")]
            property: String,
            #[tabled(rename = "Result")]
            result: String,
            #[tabled(rename = "Engine")]
            engine: String,
            #[tabled(rename = "Trace")]
            trace: String,
        }
        let cti_path = self.rp.path("cill/cti");
        recreate_dir(&cti_path)?;
        let mut results = Vec::new();
        for (i, res) in res.iter().enumerate() {
            let name = self.wsym.prop[i].clone();
            let name = name
                .strip_prefix("invariants.")
                .map(|s| s.to_string())
                .unwrap_or(name);
            // let cti_file = cti_path.join(format!("{}.cti", name));
            let strace_path = cti_path.join(format!("{}.strace", name));
            let (status, trace) = if let Some(cex) = res {
                self.save_trace(cex, true, Some(&strace_path))?;
                (
                    "Not Inductive".red().to_string(),
                    strace_path.display().to_string(),
                )
            } else {
                ("Inductive".green().to_string(), "-".to_string())
            };
            results.push(InductiveResult {
                property: name,
                result: status,
                engine: engines[i].clone().unwrap_or("-".to_string()),
                trace,
            });
        }

        let mut table = Table::new(&results);
        table.with(Style::empty()).with(
            Modify::new(Rows::first()).with(Format::content(|s| s.yellow().bold().to_string())),
        );

        println!("{}", table);

        Ok(())
    }
}
