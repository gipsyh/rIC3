use super::Transys;
use crate::transys::{self as blts};
use fol::{
    Term, TermManager,
    bitblast::{bitblast_terms, cnf_encode_terms},
};
use giputils::hash::GHashMap;
use logic_form::{DagCnf, LitVec};

impl Transys {
    pub fn bitblast(&self) -> Self {
        let mut tm = TermManager::new();
        let mut map = GHashMap::new();
        let input: Vec<Term> = bitblast_terms(self.input.iter(), &mut tm, &mut map)
            .flatten()
            .collect();
        let latch: Vec<Term> = bitblast_terms(self.latch.iter(), &mut tm, &mut map)
            .flatten()
            .collect();
        let mut init = GHashMap::new();
        for l in self.latch.iter() {
            let Some(i) = self.init.get(l) else {
                continue;
            };
            let s = l.sort();
            let l = l.bitblast(&mut tm, &mut map);
            let mut i = i.bitblast(&mut tm, &mut map);
            if s.is_array() {
                let i_len = i.len();
                assert!(l.len() & i.len() == 0);
                let ext = i[0..i_len].to_vec();
                while i.len() < l.len() {
                    i.extend_from_slice(&ext);
                }
            }
            assert!(l.len() == i.len());
            for (l, i) in l.iter().zip(i.iter()) {
                init.insert(l.clone(), i.clone());
            }
        }
        let mut next = GHashMap::new();
        for l in self.latch.iter() {
            let n = self.next.get(l).unwrap();
            let l = l.bitblast(&mut tm, &mut map);
            let n = n.bitblast(&mut tm, &mut map);
            for (l, n) in l.iter().zip(n.iter()) {
                next.insert(l.clone(), n.clone());
            }
        }
        let bad = self.bad.bitblast(&mut tm, &mut map)[0].clone();
        let constraint: Vec<Term> = bitblast_terms(self.constraint.iter(), &mut tm, &mut map)
            .flatten()
            .collect();
        Self {
            tm,
            input,
            latch,
            init,
            next,
            bad,
            constraint,
        }
    }

    pub fn to_bit_level(&self) -> blts::Transys {
        let mut dc = DagCnf::new();
        let mut map = GHashMap::new();
        let input: Vec<_> = cnf_encode_terms(self.input.iter(), &mut dc, &mut map)
            .map(|i| i.var())
            .collect();
        let latch: Vec<_> = cnf_encode_terms(self.latch.iter(), &mut dc, &mut map)
            .map(|l| l.var())
            .collect();
        let mut init = GHashMap::new();
        for l in self.latch.iter() {
            if let Some(i) = self.init.get(l) {
                let l = l.cnf_encode(&mut dc, &mut map).var();
                let i = i.cnf_encode(&mut dc, &mut map);
                assert!(i.is_constant(false) || i.is_constant(true));
                init.insert(l, i.is_constant(true));
            }
        }
        let mut next = GHashMap::new();
        for l in self.latch.iter() {
            let n = self.next.get(l).unwrap();
            let l = l.cnf_encode(&mut dc, &mut map).var();
            let n = n.cnf_encode(&mut dc, &mut map);
            next.insert(l, n);
        }
        let bad = self.bad.cnf_encode(&mut dc, &mut map);
        let constraint: LitVec =
            cnf_encode_terms(self.constraint.iter(), &mut dc, &mut map).collect();
        blts::Transys {
            input,
            latch,
            bad,
            constraint,
            rel: dc,
            next,
            init,
            rst: GHashMap::default(),
        }
    }
}
