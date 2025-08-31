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
        Sort, Term, Value,
        op::{self, Read},
    },
};
use std::{
    collections::hash_map::Entry,
    fmt::Display,
    mem::take,
    path::Path,
    process::{Command, exit},
};

impl From<&Btor> for WlTransys {
    fn from(btor: &Btor) -> Self {
        assert!(
            btor.input
                .iter()
                .all(|i| !btor.init.contains_key(&i) && !btor.next.contains_key(&i))
        );
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
    idmap: GHashMap<Term, usize>,
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
        let mut idmap = GHashMap::new();
        for (id, i) in owts.input.iter().enumerate() {
            idmap.insert(i.clone(), id);
        }
        for (id, l) in owts.latch.iter().enumerate() {
            idmap.insert(l.clone(), id);
        }
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
            idmap,
            no_next,
        }
    }
}

impl BtorFrontend {
    fn restore_state(&self, state: &[Lit], only_no_next: bool) -> Vec<String> {
        let mut map = GHashMap::new();
        for l in state.iter() {
            let (w, b) = &self.bb_rst[&l.var()];
            if only_no_next && !self.no_next.contains(w) {
                continue;
            }
            let sort = w.sort();
            let entry = map
                .entry(w.clone())
                .or_insert_with(|| Value::default_from(&w.sort()));
            match entry {
                Value::BV(bv) => bv.set(*b, l.polarity()),
                Value::Array(array) => {
                    let (_, e_len) = sort.array();
                    let idx = *b / e_len;
                    array
                        .entry(idx)
                        .or_insert_with(|| BitVec::new_with(e_len, false))
                        .set(*b % e_len, l.polarity());
                }
            }
        }
        let mut res = Vec::new();
        for (t, v) in map {
            let id = self.idmap[&t];
            match &v {
                Value::BV(bv) => res.push((self.idmap[&t], format!("{id} {bv:b}"))),
                Value::Array(array) => {
                    let (i_len, _) = t.sort().array();
                    for (i, bv) in array.iter() {
                        res.push((self.idmap[&t], format!("{id} [{:0i_len$b}] {bv:b}", *i)));
                    }
                }
            };
        }
        res.sort();
        res.into_iter().map(|(_, v)| v).collect()
    }

    fn bb_get_term(&self, i: Var) -> Term {
        let (w, b) = &self.bb_rst[&i];
        match w.sort() {
            Sort::Bv(_) => w.slice(*b, *b),
            Sort::Array(idxw, elew) => {
                let idx = b / elew;
                let eidx = b % elew;
                let read_idx = Term::bv_const_from_usize(idx, idxw);
                let read = Term::new_op(Read, [w.clone(), read_idx]);
                read.slice(eidx, eidx)
            }
        }
    }
}

impl Frontend for BtorFrontend {
    fn ts(&mut self) -> bl::Transys {
        let mut wts = self.wts.clone();
        wts.coi_refine();
        wts.simplify();
        wts.coi_refine();
        // let btor = Btor::from(&wts);
        // btor.to_file("simp.btor");
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
            map.insert(i, self.bb_get_term(i));
        }
        let mut new_latch = Vec::new();
        for l in ts.latch() {
            if let Entry::Vacant(e) = self.bb_rst.entry(l) {
                let nl = Term::new_var(Sort::Bv(1));
                e.insert((nl.clone(), 0));
                new_latch.push((l, nl));
            }
            map.insert(l, self.bb_get_term(l));
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
        let init = self.restore_state(&witness.state[0], false);
        if !init.is_empty() {
            res.push("#0".to_string());
            res.extend(init);
        }
        for t in 0..witness.len() {
            if t > 0 {
                let state = self.restore_state(&witness.state[t], true);
                if !state.is_empty() {
                    res.push(format!("#{t}"));
                    res.extend(state);
                }
            }
            let input = self.restore_state(&witness.input[t], false);
            res.push(format!("@{t}"));
            res.extend(input);
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
