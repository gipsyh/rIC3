use logic_form::LitOrdVec;
use crate::{Engine, config::Config, ic3::IC3, transys::Transys};
use std::mem::take;

pub struct Rlive {
    cfg: Config,
    ts: Transys,
    bads: Vec<LitOrdVec>,
}

impl Rlive {
    pub fn check_cycle(&self, lemma: &LitOrdVec) {

    }

    pub fn block(&mut self) {

    }
}

impl Engine for Rlive {
    fn check(&mut self) -> Option<bool> {
        assert!(self.ts.justice.len() == 1);
        let mut ts = self.ts.clone();
        ts.bad = take(&mut ts.justice);
        self.cfg.ic3.no_pred_prop = true;
        self.cfg.ic3.skip_base = true;
        let mut ic3 = IC3::new(self.cfg.clone(), ts, vec![]);

        if ic3.check().unwrap() {
            return Some(true);
        }
        let cex = ic3.witness();
        let nbad = cex.state.last().unwrap().clone();
        todo!()
    }
}

impl Rlive {
    pub fn new(cfg: Config, ts: Transys) -> Self {
        Self { cfg, ts }
    }
}
