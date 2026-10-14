mod uf;

use self::uf::Uf;
use crate::{
    BlEngine, Engine, McResult, WlCex, WlEngine, WlProof,
    config::EngineConfigBase,
    ic3::{IC3, IC3Config},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    utils::EngineCtrl,
    wltransys::{WlTransys, bitblast::BitblastMap},
};
use clap::Args;
use giputils::TerminateCtrl;
use log::info;
use logicrs::VarSymbols;
use serde::{Deserialize, Serialize};
use std::{sync::Arc, time::Instant};

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
    ctrl: Arc<EngineCtrl>,
    start: Instant,
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
        let ctrl = Arc::new(EngineCtrl::new());
        let start = Instant::now();
        let model = Self::build_model(&cfg, abstract_wts, &ctrl, start);
        Self {
            cfg,
            abstractor: Some(abstractor),
            model,
            tracer: Tracer::new(),
            ctrl,
            start,
        }
    }

    /// Builds the IC3 instance for `wts`. Every instance shares the engine's termination
    /// control and gets the time budget that is left since the engine was created.
    fn build_model(
        cfg: &CegarConfig,
        wts: WlTransys,
        ctrl: &Arc<EngineCtrl>,
        start: Instant,
    ) -> ActiveModel {
        let (ts, bb_map) = wts.bitblast_to_ts();
        let mut ic3_cfg = IC3Config::default();
        ic3_cfg.base = cfg.base.clone();
        ic3_cfg.base.time_limit = cfg
            .base
            .time_limit
            .map(|limit| limit.saturating_sub(start.elapsed().as_secs()));
        let mut ic3 = IC3::new(ic3_cfg, ts, VarSymbols::new());
        ic3.set_ctrl(ctrl.clone());
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
            let mut abstractor = self.abstractor.take().unwrap();
            let wts = match abstractor.refine(&cex) {
                Some(refined_wts) => {
                    self.abstractor = Some(abstractor);
                    refined_wts
                }
                None => {
                    info!(
                        "cegar {} abstraction cannot be refined, checking the concrete model",
                        abstractor.name()
                    );
                    abstractor.concrete_wts()
                }
            };
            self.model = Self::build_model(&self.cfg, wts, &self.ctrl, self.start);
        }
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn statistic(&mut self) {
        self.model.ic3.statistic();
    }

    fn get_ctrl(&self) -> Arc<dyn TerminateCtrl> {
        self.ctrl.clone()
    }
}

impl WlEngine for Cegar {
    fn proof(&mut self) -> WlProof {
        let proof = self.model.ic3.proof();
        let proof = self.model.bb_map.restore_proof(&self.model.wts, &proof);
        match self.abstractor.as_ref() {
            Some(abstractor) => abstractor.proof(proof),
            None => proof,
        }
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

    /// Refines the abstraction to exclude `cex`; `None` when the abstraction has no
    /// refinement for it, in which case the engine continues on the concrete model.
    fn refine(&mut self, cex: &WlCex) -> Option<WlTransys>;

    /// The transition system the abstraction was built from.
    fn concrete_wts(self: Box<Self>) -> WlTransys;

    fn proof(&self, proof: WlProof) -> WlProof;
}
