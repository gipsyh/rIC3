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
    fol::{Sort, Term, op},
};
use std::{
    collections::{BTreeMap, hash_map::Entry},
    fmt::Display,
    mem::take,
    path::Path,
    process::{Command, exit},
};

impl From<&Btor> for WlTransys {
    fn from(btor: &Btor) -> Self {
        Self {
            input: btor.input.clone(),
            latch: btor.latch.clone(),
            init: btor.init.clone(),
            next: btor.next.clone(),
            bad: btor.bad.clone(),
            constraint: btor.constraint.clone(),
            justice: Default::default(),
        }
    }
}

impl From<&WlTransys> for Btor {
    fn from(wl: &WlTransys) -> Btor {
        Btor {
            input: wl.input.clone(),
            latch: wl.latch.clone(),
            init: wl.init.clone(),
            next: wl.next.clone(),
            bad: wl.bad.clone(),
            constraint: wl.constraint.clone(),
        }
    }
}

pub struct BtorFrontend {
    owts: WlTransys,
    wts: WlTransys,
    _cfg: Config,
    // wordlevel restore
    // wb_rst: GHashMap<Term, Term>,
    // bitblast restore
    bb_rst: GHashMap<Var, (Term, usize)>,
    no_next: GHashSet<Term>,
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
        let owts = WlTransys::from(&btor);
        let mut wts = owts.clone();
        // let mut wb_rst = GHashMap::new();
        // for i in wts.input.iter() {
        //     wb_rst.insert(i.clone(), i.clone());
        // }
        // for l in wts.latch.iter() {
        //     wb_rst.insert(l.clone(), l.clone());
        // }
        let no_next = wts.remove_no_next_latch();
        Self {
            owts,
            wts,
            _cfg: cfg.clone(),
            // wb_rst,
            bb_rst: GHashMap::new(),
            no_next,
        }
    }
}

impl Frontend for BtorFrontend {
    fn ts(&mut self) -> bl::Transys {
        let mut wts = self.wts.clone();
        wts.coi_refine();
        wts.simplify();
        wts.coi_refine();
        let (bitblast, bb_rst) = wts.bitblast();
        // bitblast.coi_refine();
        // bitblast.simplify();
        // bitblast.coi_refine();
        let (ts, bbl_rst) = bitblast.lower_to_ts();
        for (k, v) in bbl_rst {
            self.bb_rst.insert(k, bb_rst[&v].clone());
        }
        ts
    }

    fn safe_certificate(&mut self, proof: Proof) -> Box<dyn Display> {
        let ts = proof.proof;
        let mut btor = self.owts.clone();
        btor.bad.clear();
        btor.constraint.clear();
        let mut map: GHashMap<Var, Term> = GHashMap::new();
        map.insert(Var::CONST, Term::bool_const(false));
        for i in ts.input() {
            let (w, b) = &self.bb_rst[&i];
            map.insert(i, w.slice(*b, *b));
        }
        let mut new_latch = Vec::new();
        for l in ts.latch() {
            if let Entry::Vacant(e) = self.bb_rst.entry(l) {
                let nl = Term::new_var(Sort::Bv(1));
                e.insert((nl.clone(), 0));
                new_latch.push((l, nl));
            }
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
                        r.push(Term::new_op_fold(
                            op::And,
                            rel.iter().map(|l| map[&l.var()].not_if(!l.polarity())),
                        ));
                    }
                }
                let n = Term::new_op_fold(op::Or, r);
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
        for (l, n) in new_latch {
            let init = ts.init(l).map(map_lit);
            let next = map_lit(ts.next(l.lit()));
            btor.add_latch(n, init, next);
        }
        Box::new(Btor::from(&btor))
    }

    fn unsafe_certificate(&mut self, mut witness: Witness) -> Box<dyn Display> {
        let mut res = vec!["sat".to_string(), "b0".to_string()];
        let mut idmap = GHashMap::new();
        let mut no_next = GHashSet::new();
        for (id, i) in self.owts.input.iter().enumerate() {
            idmap.insert(i.clone(), id);
        }
        for (id, l) in self.owts.latch.iter().enumerate() {
            idmap.insert(l.clone(), id);
            if !self.owts.next.contains_key(l) {
                no_next.insert(l.clone());
            }
        }
        for i in 0..witness.len() {
            let input = take(&mut witness.input[i]);
            for l in input {
                let (w, _) = &self.bb_rst[&l.var()];
                if self.no_next.contains(w) {
                    witness.state[i].push(l);
                } else {
                    witness.input[i].push(l);
                }
            }
        }
        let mut init = BTreeMap::new();
        for i in witness.state[0].iter() {
            let (w, b) = &self.bb_rst[&i.var()];
            let lid = idmap[w];
            init.entry(lid)
                .or_insert_with(|| BitVec::new_with(w.sort().size(), false))
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
                            .or_insert_with(|| BitVec::new_with(w.sort().size(), false))
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
                    .or_insert_with(|| BitVec::new_with(w.sort().size(), false))
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
