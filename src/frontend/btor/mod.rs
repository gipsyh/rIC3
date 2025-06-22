mod array;

use super::Frontend;
use crate::{
    Proof, Witness,
    config::Config,
    transys::{self as bl, TransysIf},
    wl::transys::WlTransys,
};
use btor::Btor;
use giputils::{
    bitvec::BitVec,
    hash::{GHashMap, GHashSet},
};
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
    fn from_btor(btor: &Btor) -> (Self, GHashMap<Term, Term>) {
        let mut rst = GHashMap::new();
        for i in btor.input.iter() {
            rst.insert(i.clone(), i.clone());
        }
        for l in btor.latch.iter() {
            rst.insert(l.clone(), l.clone());
        }
        (
            Self {
                tm: btor.tm.clone(),
                input: btor.input.clone(),
                latch: btor.latch.clone(),
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
    #[allow(unused)]
    owts: WlTransys,
    wts: WlTransys,
    _cfg: Config,
    // wordlevel restore
    wb_rst: GHashMap<Term, Term>,
    // bitblast restore
    bb_rst: GHashMap<Var, (Term, usize)>,
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
}

impl Frontend for BtorFrontend {
    fn ts(&mut self) -> bl::Transys {
        let mut wts = self.wts.clone();
        wts.coi_refine(&mut self.wb_rst);
        wts.simplify();
        wts.coi_refine(&mut self.wb_rst);
        let (bitblast, bb_rst) = wts.bitblast();
        let (ts, bbl_rst) = bitblast.lower_to_ts();
        for (k, v) in bbl_rst {
            self.bb_rst.insert(k, bb_rst[&v].clone());
        }
        ts
    }

    fn safe_certificate(&mut self, proof: Proof) -> Box<dyn Display> {
        let ts = proof.proof;
        let mut btor = self.btor.clone();
        btor.bad.clear();
        btor.constraint.clear();
        let mut map: GHashMap<Var, Term> = GHashMap::new();
        map.insert(Var::CONST, btor.tm.bool_const(false));
        for i in ts.input() {
            let (w, b) = &self.bb_rst[&i];
            map.insert(i, w.slice(*b, *b));
        }
        for l in ts.latch() {
            let (w, b) = &self.bb_rst[&l];
            map.insert(l, w.slice(*b, *b));
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
        let mut idmap = GHashMap::new();
        let mut no_next = GHashSet::new();
        for (id, i) in self.btor.input.iter().enumerate() {
            idmap.insert(i.clone(), id);
        }
        for (id, l) in self.btor.latch.iter().enumerate() {
            idmap.insert(l.clone(), id);
            if !self.btor.next.contains_key(l) {
                no_next.insert(l.clone());
            }
        }
        let mut init = BTreeMap::new();
        for i in witness.state[0].iter() {
            let (w, b) = &self.bb_rst[&i.var()];
            let lid = idmap[w];
            init.entry(lid)
                .or_insert_with(|| BitVec::new_with(w.sort().bv(), false))
                .set(*b, i.polarity());
        }
        if !init.is_empty() {
            res.push("#0".to_string());
            for (i, v) in init {
                res.push(format!("{i} {v:b}"));
            }
        }
        for t in 0..witness.len() {
            if t > 0 {
                let mut state = BTreeMap::new();
                for i in witness.state[t].iter() {
                    let (w, b) = &self.bb_rst[&i.var()];
                    if no_next.contains(w) {
                        let id = idmap[w];
                        state
                            .entry(id)
                            .or_insert_with(|| BitVec::new_with(w.sort().bv(), false))
                            .set(*b, i.polarity());
                    }
                }
                if !state.is_empty() {
                    res.push(format!("#{t}"));
                    for (i, v) in state {
                        res.push(format!("{i} {v:b}"));
                    }
                }
            }
            let mut input = BTreeMap::new();
            for i in witness.input[t].iter() {
                let (w, b) = &self.bb_rst[&i.var()];
                let id = idmap[w];
                input
                    .entry(id)
                    .or_insert_with(|| BitVec::new_with(w.sort().bv(), false))
                    .set(*b, i.polarity());
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
        cerbotor_check(model, cert)
    }
}

pub fn cerbotor_check<M: AsRef<Path>, C: AsRef<Path>>(model: M, certificate: C) -> bool {
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
