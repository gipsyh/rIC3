mod uf;

use self::uf::Uf;
use crate::{
    BlEngine, Engine, EngineCtrl, McResult, WlEngine, WlProof,
    config::EngineConfigBase,
    ic3::{IC3, IC3Config},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    wltransys::{WlTransys, bitblast::BitblastMap},
};
use clap::Args;
use logicrs::VarSymbols;
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct CegarConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,
}

impl_config_deref!(CegarConfig);

pub struct Cegar {
    cfg: CegarConfig,
    origin_wts: WlTransys,
    abstraction: Box<dyn CegarAbstractor>,
    model: ActiveModel,
    tracer: Tracer,
}

struct ActiveModel {
    ic3: IC3,
    wts: WlTransys,
    bb_map: BitblastMap,
}

impl Cegar {
    pub fn new(cfg: CegarConfig, wts: WlTransys) -> Self {
        let mut abstraction: Box<dyn CegarAbstractor> = Box::new(Uf::new());
        let abstract_wts = abstraction.abstract_wts(&wts);
        let model = Self::build_model(&cfg, abstract_wts);
        Self {
            cfg,
            origin_wts: wts,
            abstraction,
            model,
            tracer: Tracer::new(),
        }
    }

    fn build_model(cfg: &CegarConfig, wts: WlTransys) -> ActiveModel {
        let (ts, bb_map) = wts.bitblast_to_ts();
        let mut ic3_cfg = IC3Config::default();
        ic3_cfg.base = cfg.base.clone();
        let ic3 = IC3::new(ic3_cfg, ts, VarSymbols::new());
        ActiveModel { ic3, wts, bb_map }
    }
}

impl Engine for Cegar {
    fn check(&mut self) -> McResult {
        loop {
            let res = self.model.ic3.check();
            if let Some(refined_wts) = self.abstraction.refine(&self.origin_wts, res) {
                self.model = Self::build_model(&self.cfg, refined_wts);
                continue;
            }
            self.tracer.trace_state(None, res);
            return res;
        }
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn statistic(&mut self) {
        self.model.ic3.statistic();
    }

    fn get_ctrl(&self) -> EngineCtrl {
        self.model.ic3.get_ctrl()
    }
}

impl WlEngine for Cegar {
    fn proof(&mut self) -> WlProof {
        let proof = self.model.ic3.proof();
        let proof = self.model.bb_map.restore_proof(&self.model.wts, &proof);
        self.abstraction.certificate(proof)
    }
}

pub trait CegarAbstractor: Send {
    fn name(&self) -> &'static str;

    fn abstract_wts(&mut self, origin: &WlTransys) -> WlTransys;

    fn refine(&mut self, origin: &WlTransys, res: McResult) -> Option<WlTransys>;

    fn certificate(&self, proof: WlProof) -> WlProof;
}
