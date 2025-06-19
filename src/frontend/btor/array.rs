use crate::wl::transys::WlTransys;
use giputils::hash::GHashMap;
use logicrs::fol::{Sort, Term, TermType, op};
use std::{iter::once, mem::take, ops::Deref};

impl WlTransys {
    fn term_abs_array(&mut self, term: &Term, map: &mut GHashMap<Term, Term>) -> Term {
        if let Some(t) = map.get(term) {
            return t.clone();
        }
        let res = match term.deref() {
            TermType::Op(op_term) => {
                if op_term.op == op::Read {
                    let (_, e) = op_term.terms[0].sort().array();
                    let wire = self.tm.new_var(Sort::Bv(e));
                    self.input.push(wire.clone());
                    wire
                } else {
                    let terms: Vec<_> = op_term
                        .terms
                        .iter()
                        .map(|t| self.term_abs_array(t, map))
                        .collect();
                    self.tm.new_op_term(op_term.op.clone(), terms.deref())
                }
            }
            _ => term.clone(),
        };
        map.insert(term.clone(), res.clone());
        res
    }

    pub fn abs_array(&self) -> Self {
        let mut map = GHashMap::new();
        let mut res = self.clone();
        let mut init = take(&mut res.init);
        let mut next = take(&mut res.next);
        let mut constraint = take(&mut res.constraint);
        let mut bad = res.bad.clone();
        for (_, k) in init.iter_mut().chain(next.iter_mut()) {
            *k = res.term_abs_array(k, &mut map);
        }
        for t in constraint.iter_mut().chain(once(&mut bad)) {
            *t = res.term_abs_array(t, &mut map);
        }
        res.init = init;
        res.next = next;
        res.constraint = constraint;
        res.bad = bad;
        res
    }
}
