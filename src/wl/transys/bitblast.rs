use super::WlTransys;
use crate::transys::{self as blts};
use giputils::hash::GHashMap;
use logicrs::{DagCnf, LitVec};
use logicrs::{
    Lit,
    fol::{
        Term, TermManager,
        bitblast::{bitblast_terms, cnf_encode_terms},
    },
};

impl WlTransys {
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
        let bad = self.bad.bitblast(&mut tm, &mut map)[0].clone();
        let constraint: Vec<Term> = bitblast_terms(self.constraint.iter(), &mut tm, &mut map)
            .flatten()
            .collect();
        let justice: Vec<Term> = bitblast_terms(self.justice.iter(), &mut tm, &mut map)
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
            justice,
        }
    }

    pub fn to_bit_level(&self) -> blts::Transys {
        let mut dc = DagCnf::new();
        let mut map = GHashMap::new();
        let input: Vec<_> = cnf_encode_terms(self.input.iter(), &mut dc, &mut map)
            .map(|i| i.var())
            .collect();
        let mut latch: Vec<_> = cnf_encode_terms(self.latch.iter(), &mut dc, &mut map)
            .map(|l| l.var())
            .collect();
        let mut next = GHashMap::new();
        for l in self.latch.iter() {
            let n = self.next.get(l).unwrap();
            let l = l.cnf_encode(&mut dc, &mut map).var();
            let n = n.cnf_encode(&mut dc, &mut map);
            next.insert(l, n);
        }
        let mut constraint: LitVec =
            cnf_encode_terms(self.constraint.iter(), &mut dc, &mut map).collect();
        let justice: LitVec = cnf_encode_terms(self.justice.iter(), &mut dc, &mut map).collect();
        let mut init = GHashMap::new();
        let reset = dc.new_var();
        latch.push(reset);
        init.insert(reset, true);
        next.insert(reset, Lit::constant(false));
        for l in self.latch.iter() {
            if let Some(i) = self.init.get(l) {
                let l = l.cnf_encode(&mut dc, &mut map).var();
                let i = i.cnf_encode(&mut dc, &mut map);
                if i.is_constant(false) || i.is_constant(true) {
                    init.insert(l, i.is_constant(true));
                } else {
                    let eq = dc.new_xnor(l.lit(), i);
                    constraint.push(dc.new_imply(reset.lit(), eq));
                }
            }
        }
        let bad = LitVec::from([self.bad.cnf_encode(&mut dc, &mut map)]);
        blts::Transys {
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
