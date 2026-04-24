mod uf;

use crate::{
    BlEngine, Engine, EngineCtrl, McResult, WlEngine, WlProof,
    config::EngineConfigBase,
    ic3::{IC3, IC3Config},
    impl_config_deref,
    tracer::TracerIf,
    wltransys::{WlTransys, bitblast::BitblastMap},
};
use clap::Args;
use giputils::hash::GHashMap;
use log::info;
use logicrs::{VarSymbols, fol::Term};
use serde::{Deserialize, Serialize};
use uf::UfAbstractor;

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct CegarConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,
}

impl_config_deref!(CegarConfig);

pub struct Cegar {
    ic3: IC3,
    abstract_wts: WlTransys,
    bb_map: BitblastMap,
    output_subst: GHashMap<Term, Term>,
}

impl Cegar {
    pub fn new(cfg: CegarConfig, wts: WlTransys) -> Self {
        let mut uf_abstractor = UfAbstractor::new();
        let uf = uf_abstractor.abstract_transys(wts);
        let wts = uf.wts;
        info!(
            "cegar uf abstracted {} applications into {} fresh inputs and {} consistency constraints",
            uf.stats.applications, uf.stats.outputs, uf.stats.constraints,
        );
        let output_subst = uf.output_subst;

        let (ts, bb_map) = wts.bitblast_to_ts();
        let mut ic3_cfg = IC3Config::default();
        ic3_cfg.base = cfg.base;
        let ic3 = IC3::new(ic3_cfg, ts, VarSymbols::new());
        Self {
            ic3,
            abstract_wts: wts,
            bb_map,
            output_subst,
        }
    }

    fn substitute_outputs(&self, mut proof: WlProof) -> WlProof {
        proof
            .input
            .retain(|input| !self.output_subst.contains_key(input));

        let mut cache = GHashMap::new();
        for init in proof.init.values_mut() {
            *init = self.substitute_term(init, &mut cache);
        }
        for next in proof.next.values_mut() {
            *next = self.substitute_term(next, &mut cache);
        }
        for bad in proof.bad.iter_mut() {
            *bad = self.substitute_term(bad, &mut cache);
        }
        for constraint in proof.constraint.iter_mut() {
            *constraint = self.substitute_term(constraint, &mut cache);
        }
        for justice in proof.justice.iter_mut() {
            *justice = self.substitute_term(justice, &mut cache);
        }
        proof
    }

    fn substitute_term(&self, term: &Term, cache: &mut GHashMap<Term, Term>) -> Term {
        term.cached_apply(&|term| self.output_subst.get(term).cloned(), cache)
    }
}

impl Engine for Cegar {
    fn check(&mut self) -> McResult {
        self.ic3.check()
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.ic3.add_tracer(tracer);
    }

    fn statistic(&mut self) {
        self.ic3.statistic();
    }

    fn get_ctrl(&self) -> EngineCtrl {
        self.ic3.get_ctrl()
    }
}

impl WlEngine for Cegar {
    fn proof(&mut self) -> WlProof {
        let proof = self.ic3.proof();
        let proof = self.bb_map.restore_proof(&self.abstract_wts, &proof);
        self.substitute_outputs(proof)
    }
}
