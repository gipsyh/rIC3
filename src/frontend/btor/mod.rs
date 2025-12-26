mod array;

use super::Frontend;
use crate::{
    McProof, McWitness,
    transys::{self as bl},
    wltransys::{
        WlTransys,
        bitblast::BitblastMap,
        certify::{Restore, WlProof, WlWitness},
    },
};
use btor::Btor;
use giputils::{
    bitvec::BitVec,
    hash::{GHashMap, GHashSet},
};
use log::{debug, error, warn};
use logicrs::{
    VarSymbols,
    fol::{BvTermValue, Term, TermValue},
};
use std::{fmt::Display, mem::take, path::Path, process::Command};

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
    idmap: GHashMap<Term, usize>,
    no_next: GHashSet<Term>,
    rst: Restore,
    bb_rst: Option<BitblastMap>,
}

impl BtorFrontend {
    pub fn new(btor: Btor) -> Self {
        let (mut owts, symbols) = WlTransys::from_btor(&btor);
        if owts.bad.is_empty() {
            warn!("empty property in btor");
            owts.bad.push(Term::bool_const(false));
        }
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
            bb_rst: None,
        }
    }
}

impl BtorFrontend {
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
            if let Some(stripped) = line.strip_prefix('#') {
                let k = stripped.parse::<usize>().unwrap();
                if k >= witness.len() {
                    witness.resize(k + 1);
                }
                current_frame = k;
                is_state = true;
                continue;
            }
            if let Some(stripped) = line.strip_prefix('@') {
                let k = stripped.parse::<usize>().unwrap();
                if k >= witness.len() {
                    witness.resize(k + 1);
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
                if self.no_next.contains(s.t()) {
                    witness.input[k].push(s.into_bv().unwrap());
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
        wts.coi_refine();
        wts.simplify();
        wts.coi_refine();
        // let btor = Btor::from(&wts);
        // btor.to_file("simp.btor");
        let (ts, bb_rst) = wts.bitblast_to_ts();
        self.bb_rst = Some(bb_rst);
        (ts, VarSymbols::new())
    }

    fn wts(&mut self) -> (WlTransys, GHashMap<Term, String>) {
        (self.wts.clone(), self.symbols.clone())
    }

    fn certify(&mut self, model: &Path, cert: &Path) -> bool {
        cerbtora_check(model, cert)
    }

    fn safe_certificate(&mut self, proof: McProof) -> Box<dyn Display> {
        match proof {
            McProof::Bl(bl_proof) => {
                let wl_proof = self
                    .bb_rst
                    .as_ref()
                    .unwrap()
                    .restore_proof(&self.wts, &bl_proof);
                self.wl_safe_certificate(wl_proof)
            }
            McProof::Wl(wl_proof) => self.wl_safe_certificate(wl_proof),
        }
    }

    fn unsafe_certificate(&mut self, witness: crate::McWitness) -> Box<dyn Display> {
        match witness {
            McWitness::Bl(bl_witness) => {
                let wl_witness = self.bb_rst.as_ref().unwrap().restore_witness(&bl_witness);
                self.wl_unsafe_certificate(wl_witness)
            }
            McWitness::Wl(wl_witness) => self.wl_unsafe_certificate(wl_witness),
        }
    }
}

impl BtorFrontend {
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
