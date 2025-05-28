use crate::{Engine, config::Config, ic3::IC3, transys::Transys};
use std::mem::take;

pub struct Rlive {
    cfg: Config,
    ts: Transys,
}

impl Engine for Rlive {
    fn check(&mut self) -> Option<bool> {
        assert!(self.ts.justice.len() == 1);
        let mut ts = self.ts.clone();
        ts.bad = take(&mut ts.justice);
        let mut ic3 = IC3::new(self.cfg.clone(), ts, vec![]);
        dbg!(ic3.check());
        todo!()
    }
}

impl Rlive {
    pub fn new(cfg: Config, ts: Transys) -> Self {
        Self { cfg, ts }
    }
}
