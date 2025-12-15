mod array;

use super::Frontend;
use crate::{
    Proof, Witness,
    transys::{self as bl, TransysIf},
    wltransys::{
        WlTransys,
        certify::{Restore, WlProof, WlWitness},
    },
};
use btor::Btor;
use giputils::{
    bitvec::BitVec,
    hash::{GHashMap, GHashSet},
};
use log::{debug, error};
use logicrs::{
    Lit, Var, VarSymbols,
    fol::{
        BvTermValue, Sort, Term, TermValue, Value,
        op::{self, Read},
    },
};
use std::{collections::hash_map::Entry, fmt::Display, mem::take, path::Path, process::Command};

impl WlTransys {
    fn from_btor(btor: &Btor) -> (Self, GHashMap<Term, String>) {
        assert!(
            btor.input
                .iter()
                .all(|i| !btor.init.contains_key(i) && !btor.next.contains_key(i))
        );
        (
            Self {
                input: btor.input.clone(),
                latch: btor.latch.clone(),
                init: btor.init.clone(),
                next: btor.next.clone(),
                bad: btor.bad.clone(),
                constraint: btor.constraint.clone(),
                justice: Default::default(),
            },
            btor.symbols.clone(),
        )
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
            symbols: Default::default(),
        }
    }
}

#[allow(unused)]
pub struct BtorFrontend {
    owts: WlTransys,
    wts: WlTransys,
    symbols: GHashMap<Term, String>,
    // wordlevel restore
    // wb_rst: GHashMap<Term, Term>,
    // bitblast restore
    idmap: GHashMap<Term, usize>,
    no_next: GHashSet<Term>,
    rst: Restore,
}

impl BtorFrontend {
    pub fn new(btor: Btor) -> Self {
        let (owts, symbols) = WlTransys::from_btor(&btor);
        let mut idmap = GHashMap::new();
        for (id, i) in owts.input.iter().enumerate() {
            idmap.insert(i.clone(), id);
        }
        for (id, l) in owts.latch.iter().enumerate() {
            idmap.insert(l.clone(), id);
        }
        let mut wts = owts.clone();
        let mut rst = Restore::new();
        let no_next = wts.remove_no_next_latch(&mut rst);
        Self {
            owts,
            wts,
            symbols,
            idmap,
            no_next,
            rst,
        }
    }
}

impl BtorFrontend {
    fn restore_state(&self, state: &[Lit], only_no_next: bool, init: bool) -> Vec<String> {
        let mut map = GHashMap::new();
        if init {
            for (l, i) in self.owts.init.iter() {
                if let Some(c) = i.try_bv_const() {
                    map.insert(l.clone(), Value::Bv(c.clone()));
                }
            }
        }
        for l in state.iter() {
            let (w, b) = &self.rst.bb_rst[&l.var()];
            if only_no_next && !self.no_next.contains(w) {
                continue;
            }
            let sort = w.sort();
            let entry = map
                .entry(w.clone())
                .or_insert_with(|| Value::default_from(&w.sort()));
            match entry {
                Value::Bv(bv) => bv.set(*b, l.polarity()),
                Value::Array(array) => {
                    let (_, e_len) = sort.array();
                    let idx = *b / e_len;
                    array
                        .entry(idx)
                        .or_insert_with(|| BitVec::from_elem(e_len, false))
                        .set(*b % e_len, l.polarity());
                }
            }
        }
        let mut res: Vec<(usize, String)> = Vec::new();
        for (t, v) in map {
            let id = self.idmap[&t];
            match &v {
                Value::Bv(bv) => res.push((self.idmap[&t], format!("{id} {bv:b}"))),
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
        let (w, b) = &self.rst.bb_rst[&i];
        match w.sort() {
            Sort::Bv(_) => w.slice(*b, *b),
            Sort::Array(idxw, elew) => {
                let idx = b / elew;
                let eidx = b % elew;
                let read_idx = Term::bv_const(BitVec::from_usize(idxw, idx));
                let read = Term::new_op(Read, [w.clone(), read_idx]);
                read.slice(eidx, eidx)
            }
        }
    }

    pub fn deserialize_wl_unsafe_certificate(&self, content: String) -> WlWitness {
        let mut lines = content.lines();
        let first = lines.next().unwrap();
        assert_eq!(first, "sat");
        let second = lines.next().unwrap();
        assert!(second.starts_with('b'));
        let bad_id = second[1..].parse::<usize>().unwrap();
        let mut witness = WlWitness::new();
        witness.bad_id = bad_id;
        let mut current_frame = 0;
        let mut is_state = false;

        for line in lines {
            if line == "." {
                break;
            }
            if line.starts_with('#') {
                let k = line[1..].parse::<usize>().unwrap();
                if k >= witness.state.len() {
                    witness.state.resize(k + 1, Vec::new());
                }
                current_frame = k;
                is_state = true;
                continue;
            }
            if line.starts_with('@') {
                let k = line[1..].parse::<usize>().expect("Invalid frame index");
                if k >= witness.input.len() {
                    witness.input.resize(k + 1, Vec::new());
                }
                current_frame = k;
                is_state = false;
                continue;
            }
            let parts: Vec<&str> = line.split_whitespace().collect();
            assert!(parts.len() == 2);
            let id = parts[0].parse::<usize>().unwrap();
            let val = BitVec::from(parts[1]);
            if is_state {
                let term = self.owts.latch[id].clone();
                let tv = TermValue::Bv(BvTermValue::new(term, val));
                witness.state[current_frame].push(tv);
            } else {
                let term = self.owts.input[id].clone();
                let bv = BvTermValue::new(term, val);
                witness.input[current_frame].push(bv);
            }
        }
        for k in 0..witness.len() {
            for s in take(&mut witness.state[k]) {
                if self.no_next.contains(&s.t()) {
                    witness.input[k].push(s.try_bv().unwrap());
                } else {
                    witness.state[k].push(s);
                }
            }
        }
        witness
    }
}

impl Frontend for BtorFrontend {
    fn ts(&mut self) -> (bl::Transys, VarSymbols) {
        let mut wts = self.wts.clone();
        wts.coi_refine(false);
        wts.simplify();
        wts.coi_refine(false);
        // let btor = Btor::from(&wts);
        // btor.to_file("simp.btor");
        let (mut bitblast, bb_rst) = wts.bitblast();
        bitblast.coi_refine(true);
        // bitblast.simplify();
        // bitblast.coi_refine(true);
        let (ts, bbl_rst) = bitblast.lower_to_ts();
        for (k, v) in bbl_rst {
            self.rst.bb_rst.insert(k, bb_rst[&v].clone());
        }
        (ts, VarSymbols::new())
    }

    fn wts(&mut self) -> (WlTransys, GHashMap<Term, String>) {
        (self.wts.clone(), self.symbols.clone())
    }

    fn safe_certificate(&mut self, proof: Proof) -> Box<dyn Display> {
        let ts = proof.proof;
        let mut btor = self.owts.clone();
        if let Some(iv) = self.rst.init_var() {
            btor.add_latch(
                iv.clone(),
                Some(Term::bool_const(true)),
                Term::bool_const(false),
            );
        }
        btor.bad.clear();
        let mut map: GHashMap<Var, Term> = GHashMap::new();
        map.insert(Var::CONST, Term::bool_const(false));
        for i in ts.input() {
            map.insert(i, self.bb_get_term(i));
        }
        let mut new_latch = Vec::new();
        for l in ts.latch() {
            if let Entry::Vacant(e) = self.rst.bb_rst.entry(l) {
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
        for (l, n) in new_latch {
            let init = ts.init(l).map(map_lit);
            let next = map_lit(ts.next(l.lit()));
            btor.add_latch(n, init, next);
        }
        Box::new(Btor::from(&btor))
    }

    fn unsafe_certificate(&mut self, mut witness: Witness) -> Box<dyn Display> {
        let mut res = vec!["sat".to_string(), format!("b{}", witness.bad_id)];
        for i in 0..witness.len() {
            if let Some(iv) = self.rst.init_var() {
                witness.state[i].retain(|l| self.rst.bb_rst[&l.var()].0 != iv);
            }
            let input = take(&mut witness.input[i]);
            for l in input {
                let (w, _) = &self.rst.bb_rst[&l.var()];
                if self.no_next.contains(w) {
                    witness.state[i].push(l);
                } else {
                    witness.input[i].push(l);
                }
            }
        }
        let init = self.restore_state(&witness.state[0], false, true);
        if !init.is_empty() {
            res.push("#0".to_string());
            res.extend(init);
        }
        for t in 0..witness.len() {
            if t > 0 {
                let state = self.restore_state(&witness.state[t], true, false);
                if !state.is_empty() {
                    res.push(format!("#{t}"));
                    res.extend(state);
                }
            }
            let input = self.restore_state(&witness.input[t], false, false);
            res.push(format!("@{t}"));
            res.extend(input);
        }
        res.push(".\n".to_string());
        Box::new(res.join("\n"))
    }

    fn wl_safe_certificate(&mut self, proof: WlProof) -> Box<dyn Display> {
        let mut btor = self.owts.clone();
        for l in proof.input.iter() {
            if !self.idmap.contains_key(l) {
                btor.input.push(l.clone());
            }
        }
        for l in proof.latch.iter() {
            if !self.idmap.contains_key(l) {
                btor.add_latch(l.clone(), proof.proof.init(l), proof.next(l));
            }
        }
        btor.bad = proof.bad.clone();
        Box::new(Btor::from(&btor))
    }

    fn wl_unsafe_certificate(&mut self, mut witness: WlWitness) -> Box<dyn Display> {
        let mut res = vec!["sat".to_string(), format!("b{}", witness.bad_id)];
        for i in 0..witness.len() {
            if let Some(iv) = self.rst.init_var() {
                witness.state[i].retain(|tv| tv.t() != iv);
            }
            let input = take(&mut witness.input[i]);
            for lv in input {
                if self.no_next.contains(lv.t()) {
                    witness.state[i].push(TermValue::Bv(lv));
                } else {
                    witness.input[i].push(lv);
                }
            }
        }
        for (k, (input, state)) in witness.input.iter().zip(witness.state.iter()).enumerate() {
            res.push(format!("#{k}"));
            let mut idw = Vec::new();
            for tv in state {
                let id = self.idmap[tv.t()];
                match tv {
                    TermValue::Bv(bv) => idw.push((id, format!("{id} {:b}", bv.v()))),
                    TermValue::Array(_) => {
                        todo!()
                    }
                }
            }
            idw.sort();
            res.extend(idw.into_iter().map(|(_, v)| v));
            res.push(format!("@{k}"));
            let mut idw = Vec::new();
            for tv in input {
                let id = self.idmap[tv.t()];
                idw.push((id, format!("{id} {:b}", tv.v())));
            }
            idw.sort();
            res.extend(idw.into_iter().map(|(_, v)| v));
        }
        res.push(".\n".to_string());
        Box::new(res.join("\n"))
    }

    fn certify(&mut self, model: &Path, cert: &Path) -> bool {
        cerbtora_check(model, cert)
    }
}

pub fn cerbtora_check<M: AsRef<Path>, C: AsRef<Path>>(model: M, certificate: C) -> bool {
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
            "ghcr.io/gipsyh/cerbtora:latest",
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
                "cerbtora maybe not available, please `docker pull ghcr.io/gipsyh/cerbtora:latest`"
            ),
        }
        false
    }
}
