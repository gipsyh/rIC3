mod array;
mod certificate;

use super::Frontend;
use crate::{config::Config, transys as bl, wl::transys::WlTransys};
use btor::Btor;
use log::{error, warn};
use std::process::exit;

pub struct BtorFrontend {
    origin_btor: Btor,
    origin_ts: WlTransys,
    cfg: Config,
}

impl BtorFrontend {
    pub fn new(cfg: &Config) -> Self {
        let origin_btor = Btor::from_file(&cfg.model);
        let btor = origin_btor.clone();
        if btor.bad.is_empty() {
            warn!("no property to be checked");
            if let Some(certificate) = &cfg.certificate {
                btor.to_file(certificate);
            }
            exit(20);
        } else if btor.bad.len() > 1 {
            if cfg.certify {
                error!(
                    "Multiple properties detected. Cannot compress properties when certification is enabled."
                );
                panic!();
            }
            warn!("Multiple properties detected. rIC3 has compressed them into a single property.");
            todo!()
        }
        let origin_ts = WlTransys::from_btor(&origin_btor);
        Self {
            origin_btor,
            origin_ts,
            cfg: cfg.clone(),
        }
    }
}

impl Frontend for BtorFrontend {
    fn ts(&mut self) -> bl::Transys {
        let mut ts = self.origin_ts.clone();
        if self.cfg.ic3.abs_array {
            ts = ts.abs_array();
        }
        ts.coi_refine();
        dbg!(&ts);
        for _ in 0..3 {
            ts.coi_refine();
            ts.simplify();
            // ts.print_info();
        }
        let mut bitblast = ts.bitblast();
        for _ in 0..3 {
            bitblast.coi_refine();
            bitblast.simplify();
            // bitblast.print_info();
        }
        bitblast.to_bit_level()
    }

    fn certificate_safe(&mut self, _engine: &mut dyn crate::Engine) {
        if self.cfg.certificate.is_none() && !self.cfg.certify {
            return;
        }
        todo!()
    }

    fn certificate_unsafe(&mut self, _engine: &mut dyn crate::Engine) {
        if self.cfg.certificate.is_none() && !self.cfg.certify && !self.cfg.witness {
            return;
        }
        todo!()
    }
}

impl WlTransys {
    fn from_btor(btor: &Btor) -> Self {
        let mut latch = Vec::new();
        let mut input = btor.input.clone();
        for l in btor.latch.iter() {
            if btor.next.contains_key(&l) {
                latch.push(l.clone());
            } else {
                input.push(l.clone());
            }
        }
        Self {
            tm: btor.tm.clone(),
            input,
            latch,
            init: btor.init.clone(),
            next: btor.next.clone(),
            bad: btor.bad[0].clone(),
            constraint: btor.constraint.clone(),
            justice: Default::default(),
        }
    }
}
