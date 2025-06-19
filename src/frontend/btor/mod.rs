mod array;
mod certificate;

use super::Frontend;
use crate::{Proof, Witness, config::Config, transys as bl, wl::transys::WlTransys};
use btor::Btor;
use giputils::{bitvec::BitVec, hash::GHashMap};
use log::{error, warn};
use logicrs::Var;
use std::{fmt::Display, path::Path, process::exit};

pub struct BtorFrontend {
    _btor: Btor,
    owts: WlTransys,
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
            owts: wts.clone(),
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

    fn unsafe_certificate(&mut self, witness: Witness) -> Box<dyn Display> {
        let mut res = vec!["sat".to_string(), "b0".to_string()];
        let num_input = self.owts.input.len();
        let mut init = GHashMap::new();
        for i in witness.state[0].iter() {
            let (w, b) = self.bb_rst[&i.var()];
            let lid = w - num_input;
            init.entry(lid)
                .or_insert_with(|| BitVec::new_with(self.owts.latch[lid].sort().bv(), false))
                .set(b, i.polarity());
        }
        if !init.is_empty() {
            res.push("#0".to_string());
            let mut init = init.into_iter().collect::<Vec<_>>();
            init.sort_by_key(|(i, _)| *i);
            for (i, v) in init.iter() {
                res.push(format!("{i} {v}"));
            }
        }
        for (t, x) in witness.input.into_iter().enumerate() {
            let mut input = GHashMap::new();
            for i in x {
                let (w, b) = self.bb_rst[&i.var()];
                input
                    .entry(w)
                    .or_insert_with(|| BitVec::new_with(self.owts.input[w].sort().bv(), false))
                    .set(b, i.polarity());
            }
            res.push(format!("@{t}"));
            let mut input = input.into_iter().collect::<Vec<_>>();
            input.sort_by_key(|(i, _)| *i);
            for (i, v) in input.iter() {
                res.push(format!("{i} {v}"));
            }
        }
        res.push(".\n".to_string());
        Box::new(res.join("\n"))
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
