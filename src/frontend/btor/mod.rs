mod array;
mod certificate;

use super::Frontend;
use crate::{Proof, Witness, config::Config, transys as bl, wl::transys::WlTransys};
use btor::Btor;
use giputils::hash::GHashMap;
use log::{error, warn};
use logicrs::Var;
use std::{fmt::Display, path::Path, process::exit};

pub struct BtorFrontend {
    _btor: Btor,
    wts: WlTransys,
    _cfg: Config,
    // wordlevel restore
    wl_rst: GHashMap<usize, usize>,
    // bitblast restore
    bb_rst: GHashMap<Var, (usize, usize)>,
}

impl BtorFrontend {
    pub fn new(cfg: &Config) -> Self {
        let btor = Btor::from_file(&cfg.model);
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
        let wts = WlTransys::from_btor(&btor);
        let wl_rst = GHashMap::from_iter((0..wts.input.len() + wts.latch.len()).map(|i| (i, i)));
        Self {
            _btor: btor,
            wts,
            _cfg: cfg.clone(),
            wl_rst,
            bb_rst: GHashMap::new(),
        }
    }
}

impl Frontend for BtorFrontend {
    fn ts(&mut self) -> bl::Transys {
        let mut wts = self.wts.clone();
        wts.coi_refine(&mut self.wl_rst);
        wts.simplify();
        wts.coi_refine(&mut self.wl_rst);
        let (bitblast, bb_rst) = wts.bitblast();
        self.bb_rst = GHashMap::from_iter(
            bb_rst
                .into_iter()
                .map(|(i, (j, k))| (Var::new(i + 1), (self.wl_rst[&j], k))),
        );

        bitblast.lower_to_ts()
    }

    fn safe_certificate(&mut self, _proof: Proof) -> Box<dyn Display> {
        todo!()
    }

    fn unsafe_certificate(&mut self, _witness: Witness) -> Box<dyn Display> {
        todo!()
    }

    fn certify(&mut self, _model: &Path, _cert: &Path) -> bool {
        todo!()
    }
}

impl WlTransys {
    fn from_btor(btor: &Btor) -> Self {
        let mut latch = Vec::new();
        let mut input = btor.input.clone();
        for l in btor.latch.iter() {
            if btor.next.contains_key(l) {
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
