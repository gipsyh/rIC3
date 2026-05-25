use crate::cli::cill::{CIll, kind::CIllKind, utils::CIllStat};
use chrono::TimeDelta;
use giputils::logger::with_log_level;
use log::{LevelFilter, info};
use logicrs::{LitVvec, VarSymbols};
use rIC3::{
    BlEngine, Engine, McResult,
    ic3::{IC3, IC3Config},
    transys::{certify::BlCex, unroll::TransysUnroll},
};
use ratatui::style::Stylize;
use rayon::prelude::*;
use std::{fs::create_dir, time::Instant};
use tabled::{
    Table, Tabled,
    settings::{Format, Modify, Style, object::Rows},
};

impl CIll {
    pub fn check_inductive(&mut self) -> anyhow::Result<bool> {
        info!("Checking Inductiveness");
        let ind_start = Instant::now();
        let mut cfg = IC3Config::default();
        cfg.pred_prop = true;
        cfg.preproc.preproc = false;
        let num_prop = self.ts.bad.len();
        // cfg.time_limit = Some(60 + 6 * self.ts.bad.len() as u64);
        cfg.time_limit = Some(10);
        let ic3_results: Vec<_> = with_log_level(LevelFilter::Warn, || {
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
                            cfg.prop = Some(i);
                            let mut ic3 =
                                IC3::new(cfg.clone(), self.ts.clone(), VarSymbols::default());
                            let res = ic3.check();
                            let inv = ic3.invariant();
                            (matches!(res, McResult::UNSAT), inv)
                        })
                        .collect();
                    let [(sr, mut si), (ir, ii)] = ic3res.try_into().unwrap();
                    si.extend(ii);
                    (sr || ir, si)
                })
                .collect()
        });
        let mut invariants = LitVvec::new();
        let mut results = Vec::new();
        let mut ic3_proved = Vec::new();
        for (id, (r, inv)) in ic3_results.into_iter().enumerate() {
            if r {
                ic3_proved.push(id);
            }
            results.push(r);
            invariants.extend(inv);
        }
        if !ic3_proved.is_empty() {
            info!("IC3 proved {:?} prop.", ic3_proved);
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
        self.print_and_save_res(results)?;
        Ok(res)
    }

    fn print_and_save_res(&mut self, res: Vec<Option<BlCex>>) -> anyhow::Result<()> {
        #[derive(Tabled)]
        struct InductiveResult {
            #[tabled(rename = "ID")]
            id: usize,
            #[tabled(rename = "Property")]
            property: String,
            #[tabled(rename = "Result")]
            result: String,
        }
        assert!(!self.rp.has_cti());
        let cti_path = self.rp.path("cill/cti");
        create_dir(&cti_path)?;
        let mut results = Vec::new();
        for (i, res) in res.iter().enumerate() {
            let name = self.wsym.prop[i].clone();
            let status = if let Some(cex) = res {
                self.save_cex(cex, cti_path.join(format!("{}.vcd", name)))?;
                "Not Inductive".red().to_string()
            } else {
                "Inductive".green().to_string()
            };
            results.push(InductiveResult {
                id: i,
                property: name,
                result: status,
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
