use crate::{
    Engine, McProof, McResult, McWitness,
    config::{EngineConfigBase, PreprocConfig},
    ic3::{IC3, IC3Config},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    transys::{
        Transys,
        certify::{BlProof, Restore},
    },
};
use clap::{ArgAction, Args};
use giputils::logger::with_log_level;
use log::{LevelFilter, error};
use logicrs::VarSymbols;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct MultiPropConfig {
    #[command(flatten)]
    base: EngineConfigBase,

    #[command(flatten)]
    preproc: PreprocConfig,

    /// Disable parallel checking
    #[arg(long = "no-parallel", action = ArgAction::SetFalse, default_value_t = true)]
    parallel: bool,
}

impl_config_deref!(MultiPropConfig);

impl MultiPropConfig {
    pub fn validate(&self) {
        if self.prop.is_some() {
            error!("Cannot specify prop in a multi-prop engine.");
            panic!();
        }
    }
}

pub struct MultiProp {
    ots: Transys,
    ts: Transys,
    rst: Restore,
    ic3: Vec<IC3>,
    ic3_cfg: IC3Config,
    tracer: Tracer,
    parallel: bool,
    results: Vec<McResult>,
}

impl MultiProp {
    pub fn new(cfg: MultiPropConfig, ts: Transys) -> Self {
        cfg.validate();
        let ots = ts.clone();
        let rst = Restore::new(&ts);
        let (mut ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        ts.remove_gate_init(&mut rst);
        let mut ic3_cfg = IC3Config::default();
        ic3_cfg.local_proof = true;
        ic3_cfg.pred_prop = true;
        ic3_cfg.inn = true;
        ic3_cfg.preproc.frts = false;
        ic3_cfg.preproc.scorr = false;
        let parallel = cfg.parallel;
        Self {
            ots,
            results: vec![McResult::default(); ts.bad.len()],
            ts,
            rst,
            ic3: Vec::new(),
            ic3_cfg,
            tracer: Tracer::new(),
            parallel,
        }
    }
}

impl Engine for MultiProp {
    fn check(&mut self) -> McResult {
        if self.parallel {
            let results: Vec<_> = with_log_level(LevelFilter::Warn, || {
                (0..self.ts.bad.len())
                    .into_par_iter()
                    .map(|i| {
                        let mut cfg = self.ic3_cfg.clone();
                        cfg.prop = Some(i);
                        let mut ic3 = IC3::new(cfg, self.ts.clone(), VarSymbols::default());
                        let result = ic3.check();
                        (ic3, result)
                    })
                    .collect()
            });
            for (bad, (ic3, result)) in results.into_iter().enumerate() {
                self.ic3.push(ic3);
                self.results[bad] = result;
                match result {
                    McResult::Safe => (),
                    McResult::Unsafe(_) => return result,
                    McResult::Unknown(_) => unreachable!(),
                }
            }
        } else {
            for i in 0..self.ts.bad.len() {
                let mut cfg = self.ic3_cfg.clone();
                cfg.prop = Some(i);
                let mut ic3 = IC3::new(cfg, self.ts.clone(), VarSymbols::default());
                let result = ic3.check();
                self.ic3.push(ic3);
                self.results[i] = result;
                match result {
                    McResult::Safe => (),
                    McResult::Unsafe(_) => return result,
                    McResult::Unknown(_) => todo!(),
                }
            }
        }
        McResult::Safe
    }

    fn proof(&mut self) -> McProof {
        let mut proof = BlProof {
            proof: self.ts.clone(),
        };
        for ic3 in self.ic3.iter_mut() {
            let subp = ic3.proof().into_bl().unwrap();
            proof.merge(&subp, &self.ts);
        }
        let proof = self.rst.restore_proof(proof, &self.ots);
        McProof::Bl(proof)
    }

    fn witness(&mut self) -> McWitness {
        let bid = self.results.iter().position(|r| r.is_unsafe()).unwrap();
        let wit = self.ic3[bid].witness().into_bl().unwrap();
        let wit = self.rst.restore_witness(&wit);
        McWitness::Bl(wit)
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }
}
