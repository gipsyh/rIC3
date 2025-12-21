use super::WlTransys;
use crate::transys::Transys;
use giputils::hash::GHashMap;
use logicrs::{DagCnf, LitVec};
use logicrs::{
    Var,
    fol::{
        Term,
        bitblast::{bitblast_terms, cnf_encode_terms},
    },
};
use std::ops::{Deref, DerefMut};

impl WlTransys {
    fn bitblast(&self) -> (Self, GHashMap<Term, (Term, usize)>) {
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

    pub fn bitblast_to_ts(&self) -> (Transys, BitblastRestore) {
        let (mut bitblast, bb_rst) = self.bitblast();
        bitblast.coi_refine();
        let (ts, bbl_rst) = bitblast.lower_to_ts();
        let mut rst_bb_rst = GHashMap::new();
        for (k, v) in bbl_rst {
            rst_bb_rst.insert(k, bb_rst[&v].clone());
        }
        (ts, BitblastRestore(rst_bb_rst))
    }
}

#[derive(Debug, Default, Clone)]
pub struct BitblastRestore(GHashMap<Var, (Term, usize)>);

impl Deref for BitblastRestore {
    type Target = GHashMap<Var, (Term, usize)>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for BitblastRestore {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
