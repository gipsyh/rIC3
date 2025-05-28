use crate::{Engine, config::Config, transys::Transys};

pub struct Rlive {
    cfg: Config,
    ts: Transys,
}

impl Engine for Rlive {
    fn check(&mut self) -> Option<bool> {
        assert!(self.ts.justice.len() == 1);
        let mut ts = self.ts.clone();
        todo!()

    }
}

impl Rlive {
    pub fn new(cfg: Config, ts: Transys) -> Self {
        Self { cfg, ts }
    }
}
