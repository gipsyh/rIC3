use super::WlTransys;
use crate::{
    transys::{
        Transys, TransysIf,
        certify::{BlProof, BlWitness},
    },
    wltransys::certify::{WlProof, WlWitness},
};
use giputils::{bitvec::BitVec, hash::GHashMap};
use logicrs::{
    DagCnf, Lbool, LboolVec, Lit, LitVec, Var,
    fol::{
        BvTermValue, Sort, Term, TermValue, TermVec, Value,
        bitblast::{bitblast_terms, cnf_encode_terms},
        op,
    },
};

impl WlTransys {
    fn bitblast(&self) -> (Self, GHashMap<Term, TermVec>, GHashMap<Term, (Term, usize)>) {
        let mut rst = GHashMap::new();
        let mut map = GHashMap::new();
        let mut input = Vec::new();
        for x in self.input.iter() {
            let bb = x.bitblast(&mut map);
            for (j, b) in bb.into_iter().enumerate() {
                rst.insert(b.clone(), (x.clone(), j));
                input.push(b);
            }
        }
        let mut latch = Vec::new();
        for x in self.latch.iter() {
            let bb = x.bitblast(&mut map);
            for (j, b) in bb.into_iter().enumerate() {
                rst.insert(b.clone(), (x.clone(), j));
                latch.push(b);
            }
        }
        let mut init = GHashMap::new();
        let mut next = GHashMap::new();
        for l in self.latch.iter() {
            if let Some(n) = self.next.get(l) {
                let l = l.bitblast(&mut map);
                let n = n.bitblast(&mut map);
                for (l, n) in l.iter().zip(n.iter()) {
                    next.insert(l.clone(), n.clone());
                }
            }
            if let Some(i) = self.init.get(l) {
                let s = l.sort();
                let l = l.bitblast(&mut map);
                let mut i = i.bitblast(&mut map);
                if s.is_array() {
                    assert!(l.len() % i.len() == 0);
                    let ext = i[0..i.len()].to_vec();
                    while i.len() < l.len() {
                        i.extend_from_slice(&ext);
                    }
                }
                assert!(l.len() == i.len());
                for (l, i) in l.iter().zip(i.iter()) {
                    init.insert(l.clone(), i.clone());
                }
            }
        }
        let bad: Vec<Term> = bitblast_terms(self.bad.iter(), &mut map)
            .flatten()
            .collect();
        let constraint: Vec<Term> = bitblast_terms(self.constraint.iter(), &mut map)
            .flatten()
            .collect();
        let justice: Vec<Term> = bitblast_terms(self.justice.iter(), &mut map)
            .flatten()
            .collect();
        let mut nmap = GHashMap::new();
        for v in self.input.iter().chain(self.latch.iter()) {
            nmap.insert(v.clone(), map[v].clone());
        }
        (
            Self {
                input,
                latch,
                init,
                next,
                bad,
                constraint,
                justice,
            },
            nmap,
            rst,
        )
    }

    fn lower_to_ts(&self) -> (Transys, GHashMap<Var, Term>) {
        let mut rst = GHashMap::new();
        let mut dc = DagCnf::new();
        let mut map = GHashMap::new();
        let mut input = Vec::new();
        for x in self.input.iter() {
            let v = x.cnf_encode(&mut dc, &mut map).var();
            rst.insert(v, x.clone());
            input.push(v);
        }
        let mut latch = Vec::new();
        for x in self.latch.iter() {
            let v = x.cnf_encode(&mut dc, &mut map).var();
            rst.insert(v, x.clone());
            latch.push(v);
        }
        let mut next = GHashMap::new();
        for l in self.latch.iter() {
            if let Some(n) = self.next.get(l) {
                let l = l.cnf_encode(&mut dc, &mut map).var();
                let n = n.cnf_encode(&mut dc, &mut map);
                next.insert(l, n);
            }
        }
        let constraint: LitVec =
            cnf_encode_terms(self.constraint.iter(), &mut dc, &mut map).collect();
        let justice: LitVec = cnf_encode_terms(self.justice.iter(), &mut dc, &mut map).collect();
        let mut init = GHashMap::new();
        for l in self.latch.iter() {
            if let Some(i) = self.init.get(l) {
                let l = l.cnf_encode(&mut dc, &mut map).var();
                let i = i.cnf_encode(&mut dc, &mut map);
                init.insert(l, i);
            }
        }
        let bad: LitVec = cnf_encode_terms(self.bad.iter(), &mut dc, &mut map).collect();
        (
            Transys {
                input,
                latch,
                bad,
                constraint,
                rel: dc,
                next,
                init,
                justice,
            },
            rst,
        )
    }

    pub fn bitblast_to_ts(&self) -> (Transys, BitblastMap) {
        let (bitblast, bb_map, bb_rst) = self.bitblast();
        let (ts, v2t) = bitblast.lower_to_ts();
        let t2v: GHashMap<Term, Var> = v2t.iter().map(|(&x, y)| (y.clone(), x)).collect();
        let w2b: GHashMap<Term, Vec<Var>> = bb_map
            .iter()
            .map(|(t, tv)| {
                let tv: Vec<Var> = tv.iter().map(|t| t2v[t]).collect();
                (t.clone(), tv)
            })
            .collect();
        let mut b2w = GHashMap::new();
        for (k, v) in v2t {
            b2w.insert(k, bb_rst[&v].clone());
        }
        (ts, BitblastMap { w2b, b2w })
    }
}

#[derive(Debug, Default, Clone)]
pub struct BitblastMap {
    b2w: GHashMap<Var, (Term, usize)>,
    w2b: GHashMap<Term, Vec<Var>>,
}

impl BitblastMap {
    pub fn map(self, t: &Term) -> Vec<Var> {
        self.w2b[t].clone()
    }

    pub fn restore(&self, v: Var) -> (Term, usize) {
        self.b2w[&v].clone()
    }

    pub fn try_restore(&self, v: Var) -> Option<(Term, usize)> {
        self.b2w.get(&v).cloned()
    }

    pub fn add_map(&mut self, v: Var, t: &Term) {
        assert!(t.sort().bv() == 1);
        assert!(self.b2w.insert(v, (t.clone(), 0)).is_none());
        assert!(self.w2b.insert(t.clone(), vec![v]).is_none());
    }
}

impl BitblastMap {
    pub fn restore_lits(&self, state: &[Lit]) -> Vec<TermValue> {
        let mut map = GHashMap::new();
        for l in state.iter() {
            let (w, b) = &self.restore(l.var());
            let sort = w.sort();
            let entry = map
                .entry(w.clone())
                .or_insert_with(|| Value::default_from(&w.sort()));
            match entry {
                Value::Bv(bv) => bv.set_bool(*b, l.polarity()),
                Value::Array(array) => {
                    let (_, e_len) = sort.array();
                    let idx = *b / e_len;
                    array
                        .entry(idx)
                        .or_insert_with(|| LboolVec::from_elem(Lbool::NONE, e_len))
                        .set_bool(*b % e_len, l.polarity());
                }
            }
        }
        map.into_iter().map(|(t, v)| TermValue::new(t, v)).collect()
    }

    pub fn map_termval(&self, tv: &BvTermValue) -> LitVec {
        let b = &self.w2b[tv.t()];
        b.iter()
            .zip(tv.v().iter())
            .filter_map(|(s, v)| (!v).is_none().then(|| Lit::new(*s, v.is_true())))
            .collect()
    }

    pub fn restore_var(&self, v: Var) -> Term {
        let (w, b) = &self.restore(v);
        match w.sort() {
            Sort::Bv(_) => w.slice(*b, *b),
            Sort::Array(idxw, elew) => {
                let idx = b / elew;
                let eidx = b % elew;
                let read_idx = Term::bv_const(BitVec::from_usize(idxw, idx));
                let read = Term::new_op(op::Read, [w.clone(), read_idx]);
                read.slice(eidx, eidx)
            }
        }
    }

    pub fn restore_witness(&self, witness: &BlWitness) -> WlWitness {
        let mut res = WlWitness::new();
        res.bad_id = witness.bad_id;
        for t in 0..witness.len() {
            res.input.push(
                self.restore_lits(&witness.input[t])
                    .into_iter()
                    .map(|t| t.into_bv())
                    .collect(),
            );
            res.state.push(self.restore_lits(&witness.state[t]));
        }
        res
    }

    pub fn bitblast_witness(&self, witness: &WlWitness) -> BlWitness {
        let mut res = BlWitness::new();
        res.bad_id = witness.bad_id;
        for t in 0..witness.len() {
            let lv: LitVec = witness.input[t]
                .iter()
                .flat_map(|t| self.map_termval(t))
                .collect();
            res.input.push(lv);
            let lv: LitVec = witness.state[t]
                .iter()
                .flat_map(|t| self.map_termval(&t.into_bv()))
                .collect();
            res.state.push(lv);
        }
        res
    }

    pub fn restore_proof(&self, wts: &WlTransys, proof: &BlProof) -> WlProof {
        let mut res = wts.clone();
        res.bad.clear();
        let mut new_latch = Vec::new();
        let ts = &proof.proof;
        let mut map: GHashMap<Var, Term> = GHashMap::new();
        map.insert(Var::CONST, Term::bool_const(false));
        for i in ts.input() {
            map.insert(i, self.restore_var(i));
        }
        for l in ts.latch() {
            if self.try_restore(l).is_none() {
                let nl = Term::new_var(Sort::Bv(1));
                new_latch.push((l, nl.clone()));
                map.insert(l, nl);
            } else {
                map.insert(l, self.restore_var(l));
            }
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
        for (l, n) in new_latch {
            let init = ts.init(l).map(map_lit);
            let next = map_lit(ts.next(l.lit()));
            res.add_latch(n, init, next);
        }
        for &b in ts.bad.iter() {
            res.bad.push(map_lit(b));
        }
        for &c in ts.constraint.iter() {
            res.constraint.push(map_lit(c));
        }
        for &j in ts.justice.iter() {
            res.justice.push(map_lit(j));
        }
        WlProof { proof: res }
    }
}
