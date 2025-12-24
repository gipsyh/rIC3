use crate::{
    Engine, McProof, McResult,
    config::{EngineConfigBase, PreprocConfig},
    ic3::{IC3, IC3Config},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    transys::{
        Transys,
        certify::{BlProof, Restore},
    },
};
use clap::Args;
use logicrs::{LitVec, VarSymbols};
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct MultiPropConfig {
    #[command(flatten)]
    base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,
}

impl_config_deref!(MultiPropConfig);

pub struct MultiProp {
    ots: Transys,
    ts: Transys,
    rst: Restore,
    ic3: Vec<IC3>,
    ic3_cfg: IC3Config,
    tracer: Tracer,
}

impl MultiProp {
    pub fn new(cfg: MultiPropConfig, ts: Transys) -> Self {
        let ots = ts.clone();
        let rst = Restore::new(&ts);
        let (mut ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        ts.remove_gate_init(&mut rst);
        let mut ic3_cfg = IC3Config::default();
        // ic3_cfg.time_limit = Some(200);
        ic3_cfg.local_proof = true;
        ic3_cfg.pred_prop = true;
        ic3_cfg.preproc.preproc = false;
        Self {
            ots,
            ts,
            rst,
            ic3: Vec::new(),
            ic3_cfg,
            tracer: Tracer::new(),
        }
    }
}

impl Engine for MultiProp {
    fn check(&mut self) -> McResult {
        for i in 0..self.ts.bad.len() {
            let mut cfg = self.ic3_cfg.clone();
            cfg.prop = Some(i);
            let mut ic3 = IC3::new(cfg, self.ts.clone(), VarSymbols::default());
            match ic3.check() {
                McResult::Safe => (),
                McResult::Unsafe(_) => todo!(),
                McResult::Unknown(_) => todo!(),
            }
            self.ic3.push(ic3);
        }
        McResult::Safe
    }

    fn proof(&mut self) -> McProof {
        let mut proof = self.ots.clone();
        proof.bad.clear();
        for ic3 in self.ic3.iter_mut() {
            let subp = ic3.proof().into_bl().unwrap().proof;
            assert!(subp.input == proof.input);
            assert!(subp.latch == proof.latch);
            let mut map = self.rst.vmap.clone();
            proof.rel.migrate(&subp.rel, subp.bad[0].var(), &mut map);
            dbg!(proof.rel.max_var());
            proof.bad.push(map.lit_map(subp.bad[0]).unwrap());
        }
        proof.bad = LitVec::from(proof.rel.new_or(proof.bad));
        McProof::Bl(BlProof { proof })
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }
}
