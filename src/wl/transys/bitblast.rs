use super::WlTransys;
use crate::transys::Transys;
use giputils::hash::GHashMap;
use logicrs::fol::{
    Term, TermManager,
    bitblast::{bitblast_terms, cnf_encode_terms},
};
use logicrs::{DagCnf, LitVec};

impl WlTransys {
    pub fn bitblast(&self) -> (Self, GHashMap<usize, (usize, usize)>) {
        let mut rst = GHashMap::new();
        let mut tm = TermManager::new();
        let mut map = GHashMap::new();
        let onum_input = self.input.len();
        let mut input = Vec::new();
        for (i, x) in self.input.iter().enumerate() {
            let bb = x.bitblast(&mut tm, &mut map);
            for (j, b) in bb.into_iter().enumerate() {
                rst.insert(input.len(), (i, j));
                input.push(b);
            }
        }
        let mut latch = Vec::new();
        for (mut i, x) in self.latch.iter().enumerate() {
            i += onum_input;
            let bb = x.bitblast(&mut tm, &mut map);
            for (j, b) in bb.into_iter().enumerate() {
                rst.insert(latch.len() + input.len(), (i, j));
                latch.push(b);
            }
        }
        let mut init = GHashMap::new();
        for l in self.latch.iter() {
            let Some(i) = self.init.get(l) else {
                continue;
            };
            let s = l.sort();
            let l = l.bitblast(&mut tm, &mut map);
            let mut i = i.bitblast(&mut tm, &mut map);
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
        let mut next = GHashMap::new();
        for l in self.latch.iter() {
            let n = self.next.get(l).unwrap();
            let l = l.bitblast(&mut tm, &mut map);
            let n = n.bitblast(&mut tm, &mut map);
            for (l, n) in l.iter().zip(n.iter()) {
                next.insert(l.clone(), n.clone());
            }
        }
        let bad: Vec<Term> = bitblast_terms(self.bad.iter(), &mut tm, &mut map)
            .flatten()
            .collect();
        let constraint: Vec<Term> = bitblast_terms(self.constraint.iter(), &mut tm, &mut map)
            .flatten()
            .collect();
        let justice: Vec<Term> = bitblast_terms(self.justice.iter(), &mut tm, &mut map)
            .flatten()
            .collect();
        (
            Self {
                tm,
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

    pub fn lower_to_ts(&self) -> Transys {
        let mut dc = DagCnf::new();
        let mut map = GHashMap::new();
        let input: Vec<_> = cnf_encode_terms(self.input.iter(), &mut dc, &mut map)
            .map(|i| i.var())
            .collect();
        let latch: Vec<_> = cnf_encode_terms(self.latch.iter(), &mut dc, &mut map)
            .map(|l| l.var())
            .collect();
        let mut next = GHashMap::new();
        for l in self.latch.iter() {
            let n = self.next.get(l).unwrap();
            let l = l.cnf_encode(&mut dc, &mut map).var();
            let n = n.cnf_encode(&mut dc, &mut map);
            next.insert(l, n);
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
        Transys {
            input,
            latch,
            bad,
            constraint,
            rel: dc,
            next,
            init,
            justice,
        }
    }
}
