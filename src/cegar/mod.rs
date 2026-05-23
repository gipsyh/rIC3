mod uf;

use self::uf::Uf;
use crate::{
    BlEngine, Engine, McResult, WlCex, WlEngine, WlProof,
    config::EngineConfigBase,
    ic3::{IC3, IC3Config},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    wltransys::{WlTransys, bitblast::BitblastMap},
};
use clap::Args;
use giputils::TerminateCtrl;
use logicrs::VarSymbols;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct CegarConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,
}

impl_config_deref!(CegarConfig);

pub struct Cegar {
    cfg: CegarConfig,
    abstractor: Option<Box<dyn CegarAbstractor>>,
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
        let mut abstractor: Box<dyn CegarAbstractor> = Box::new(Uf::new(wts));
        let abstract_wts = abstractor.abstract_wts();
        let model = Self::build_model(&cfg, abstract_wts);
        Self {
            cfg,
            abstractor: Some(abstractor),
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
            if !res.is_sat() || self.abstractor.is_none() {
                self.tracer.trace_state(None, res);
                return res;
            }
            let bl_cex = self.model.ic3.cex();
            let cex = self.model.bb_map.restore_cex(&bl_cex);
            if let Some(refined_wts) = self.abstractor.as_mut().unwrap().refine(&cex) {
                self.model = Self::build_model(&self.cfg, refined_wts);
            } else {
                self.abstractor = None;
            }
        }
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn statistic(&mut self) {
        self.model.ic3.statistic();
    }

    fn get_ctrl(&self) -> Arc<dyn TerminateCtrl> {
        self.model.ic3.get_ctrl()
    }
}

impl WlEngine for Cegar {
    fn proof(&mut self) -> WlProof {
        let proof = self.model.ic3.proof();
        let proof = self.model.bb_map.restore_proof(&self.model.wts, &proof);
        self.abstractor.as_mut().unwrap().proof(proof)
    }

    fn cex(&mut self) -> WlCex {
        debug_assert!(self.abstractor.is_none());
        let bl_cex = self.model.ic3.cex();
        self.model.bb_map.restore_cex(&bl_cex)
    }
}

pub trait CegarAbstractor: Send {
    fn name(&self) -> &'static str;

    fn abstract_wts(&mut self) -> WlTransys;

    fn refine(&mut self, cex: &WlCex) -> Option<WlTransys>;

    fn proof(&self, proof: WlProof) -> WlProof;
}
