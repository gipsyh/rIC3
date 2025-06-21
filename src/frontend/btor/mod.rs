mod array;

use super::Frontend;
use crate::{
    Proof, Witness,
    config::Config,
    transys::{self as bl, Transys, TransysIf},
    wl::transys::WlTransys,
};
use btor::Btor;
use giputils::{bitvec::BitVec, hash::GHashMap};
use log::{debug, error, warn};
use logicrs::{
    Lit, Var,
    fol::{
        Term,
        op::{And, Or},
    },
};
use std::{
    collections::BTreeMap,
    fmt::Display,
    path::Path,
    process::{Command, exit},
};

impl WlTransys {
    fn from_btor(btor: &Btor) -> (Self, GHashMap<usize, usize>) {
        let mut rst = GHashMap::new();
        let mut latch = Vec::new();
        let mut input = btor.input.clone();
        for i in 0..btor.input.len() {
            rst.insert(i, i);
        }
        for (i, l) in btor.latch.iter().enumerate() {
            if !btor.next.contains_key(l) {
                rst.insert(input.len(), i + btor.input.len());
                input.push(l.clone());
            }
        }
        for (i, l) in btor.latch.iter().enumerate() {
            if btor.next.contains_key(l) {
                rst.insert(input.len() + latch.len(), i + btor.input.len());
                latch.push(l.clone());
            }
        }
        (
            Self {
                tm: btor.tm.clone(),
                input,
                latch,
                init: btor.init.clone(),
                next: btor.next.clone(),
                bad: btor.bad.clone(),
                constraint: btor.constraint.clone(),
                justice: Default::default(),
            },
            rst,
        )
    }
}

pub struct BtorFrontend {
    btor: Btor,
    owts: WlTransys,
    wts: WlTransys,
    _cfg: Config,
    // wordlevel restore
    wb_rst: GHashMap<usize, usize>,
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
        let (wts, wb_rst) = WlTransys::from_btor(&btor);
        Self {
            btor,
            owts: wts.clone(),
            wts,
            _cfg: cfg.clone(),
            wb_rst,
            bb_rst: GHashMap::new(),
        }
    }

    pub fn btor_certifate(&self, ts: &Transys) -> WlTransys {
        let mut wts = WlTransys::new(self.owts.tm.clone());
        wts.input = self.owts.input.clone();
        wts.latch = self.owts.latch.clone();
        wts.init = self.owts.init.clone();
        wts.next = self.owts.next.clone();
        let mut map: GHashMap<Var, Term> = GHashMap::new();
        map.insert(Var::CONST, wts.tm.bool_const(false));
        for i in ts.input() {
            let (w, b) = self.bb_rst[&i];
            map.insert(i, wts.input[w].slice(b, b));
        }
        for l in ts.latch() {
            let (mut w, b) = self.bb_rst[&l];
            w -= ts.input.len();
            map.insert(l, wts.latch[w].slice(b, b));
        }

        for (v, rel) in ts.rel.iter() {
            if ts.rel.has_rel(v) && !v.is_constant() {
                assert!(!map.contains_key(&v));
                let mut r = Vec::new();
                for rel in rel {
                    let last = rel.last();
                    assert!(last.var() == v);
                    if last.polarity() {
                        let mut rel = !rel;
                        rel.pop();
                        r.push(wts.tm.new_op_term(
                            And,
                            rel.iter().map(|l| map[&l.var()].not_if(!l.polarity())),
                        ));
                    }
                }
                let n = wts.tm.new_op_term(Or, r);
                map.insert(v, n);
            }
        }
        let map_lit = |l: Lit| map[&l.var()].not_if(!l.polarity());
        for &b in ts.bad.iter() {
            wts.bad.push(map_lit(b));
        }
        for c in ts.constraint() {
            wts.constraint.push(map_lit(c));
        }
        if !ts.justice.is_empty() {
            wts.justice = ts.justice.iter().map(|&j| map_lit(j)).collect();
        }
        wts
    }
}

impl Frontend for BtorFrontend {
    fn ts(&mut self) -> bl::Transys {
        let mut wts = self.wts.clone();
        wts.coi_refine(&mut self.wb_rst);
        wts.simplify();
        wts.coi_refine(&mut self.wb_rst);
        let (bitblast, bb_rst) = wts.bitblast();
        self.bb_rst = GHashMap::from_iter(
            bb_rst
                .into_iter()
                .map(|(i, (j, k))| (Var::new(i + 1), (self.wb_rst[&j], k))),
        );
        bitblast.lower_to_ts()
    }

    fn safe_certificate(&mut self, proof: Proof) -> Box<dyn Display> {
        let ts = proof.proof;
        let mut btor = self.btor.clone();
        btor.bad.clear();
        btor.constraint.clear();
        let mut map: GHashMap<Var, Term> = GHashMap::new();
        map.insert(Var::CONST, btor.tm.bool_const(false));
        for i in ts.input() {
            let (w, b) = self.bb_rst[&i];
            map.insert(i, btor.input[w].slice(b, b));
        }
        for l in ts.latch() {
            let (mut w, b) = self.bb_rst[&l];
            w -= ts.input.len();
            map.insert(l, btor.latch[w].slice(b, b));
        }
        for (v, rel) in ts.rel.iter() {
            if ts.rel.has_rel(v) && !v.is_constant() {
                assert!(!map.contains_key(&v));
                let mut r = Vec::new();
                for rel in rel {
                    let last = rel.last();
                    assert!(last.var() == v);
                    if last.polarity() {
                        let mut rel = !rel;
                        rel.pop();
                        r.push(btor.tm.new_op_terms_fold(
                            And,
                            rel.iter().map(|l| map[&l.var()].not_if(!l.polarity())),
                        ));
                    }
                }
                let n = btor.tm.new_op_terms_fold(Or, r);
                map.insert(v, n);
            }
        }
        let map_lit = |l: Lit| map[&l.var()].not_if(!l.polarity());
        for &b in ts.bad.iter() {
            btor.bad.push(map_lit(b));
        }
        for c in ts.constraint() {
            btor.constraint.push(map_lit(c));
        }
        Box::new(btor)
    }

    fn unsafe_certificate(&mut self, witness: Witness) -> Box<dyn Display> {
        let mut res = vec!["sat".to_string(), "b0".to_string()];
        let num_input = self.owts.input.len();
        let mut init = BTreeMap::new();
        for i in witness.state[0].iter() {
            let (w, b) = self.bb_rst[&i.var()];
            let lid = w - num_input;
            init.entry(lid)
                .or_insert_with(|| BitVec::new_with(self.owts.latch[lid].sort().bv(), false))
                .set(b, i.polarity());
        }
        if !init.is_empty() {
            res.push("#0".to_string());
            for (i, v) in init {
                res.push(format!("{i} {v:b}"));
            }
        }
        for (t, x) in witness.input.into_iter().enumerate() {
            let mut input = BTreeMap::new();
            for i in x {
                let (w, b) = self.bb_rst[&i.var()];
                input
                    .entry(w)
                    .or_insert_with(|| BitVec::new_with(self.owts.input[w].sort().bv(), false))
                    .set(b, i.polarity());
            }
            res.push(format!("@{t}"));
            for (i, v) in input {
                res.push(format!("{i} {v:b}"));
            }
        }
        res.push(".\n".to_string());
        Box::new(res.join("\n"))
    }

    fn certify(&mut self, model: &Path, cert: &Path) -> bool {
        certobor_check(model, cert)
    }
}

pub fn certobor_check<M: AsRef<Path>, C: AsRef<Path>>(model: M, certificate: C) -> bool {
    let certificate = certificate.as_ref();
    let output = Command::new("docker")
        .args([
            "run",
            "--rm",
            "--pull=never",
            "-v",
            &format!("{}:{}", model.as_ref().display(), model.as_ref().display()),
            "-v",
            &format!("{}:{}", certificate.display(), certificate.display()),
            "ghcr.io/gipsyh/cerbotor:latest",
        ])
        .arg(model.as_ref())
        .arg(certificate)
        .output()
        .unwrap();
    if output.status.success() {
        true
    } else {
        debug!("{}", String::from_utf8_lossy(&output.stdout));
        debug!("{}", String::from_utf8_lossy(&output.stderr));
        match output.status.code() {
            Some(1) => (),
            _ => error!(
                "cerbotor maybe not avaliable, please `docker pull ghcr.io/gipsyh/cerbotor:latest`"
            ),
        }
        false
    }
}
