use super::WlTransys;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{Term, TermType};
use std::{mem::take, ops::Deref};

impl WlTransys {
    pub fn coi_refine(&mut self, rst: &mut GHashMap<usize, usize>) {
        let mut queue = self.constraint.clone();
        queue.push(self.bad.clone());
        let mut touch: GHashSet<Term> = GHashSet::from_iter(queue.iter().cloned());
        while let Some(t) = queue.pop() {
            match &t.deref() {
                TermType::Const(_) => (),
                TermType::Var(_) => {
                    if let Some(n) = self.next.get(&t) {
                        if touch.insert(n.clone()) {
                            queue.push(n.clone());
                        }
                    }
                    if let Some(i) = self.init.get(&t) {
                        if touch.insert(i.clone()) {
                            queue.push(i.clone());
                        }
                    }
                }
                TermType::Op(op) => {
                    for s in op.terms.iter() {
                        if touch.insert(s.clone()) {
                            queue.push(s.clone());
                        }
                    }
                }
            };
        }
        let onum_input = self.input.len();
        let mut nrst = GHashMap::new();
        for (i, x) in take(&mut self.input).into_iter().enumerate() {
            if touch.contains(&x) {
                nrst.insert(self.input.len(), rst[&i]);
                self.input.push(x);
            }
        }
        for (i, x) in take(&mut self.latch).into_iter().enumerate() {
            if touch.contains(&x) {
                nrst.insert(self.input.len() + self.latch.len(), rst[&(i + onum_input)]);
                self.latch.push(x);
            }
        }
        self.init.retain(|k, _| touch.contains(k));
        self.next.retain(|k, _| touch.contains(k));
    }

    pub fn simplify(&mut self) {
        let mut map = GHashMap::new();
        for (_, n) in self.next.iter_mut() {
            *n = n.simplify(&mut self.tm, &mut map);
        }
        for c in self.constraint.iter_mut() {
            *c = c.simplify(&mut self.tm, &mut map);
        }
        self.bad = self.bad.simplify(&mut self.tm, &mut map);
    }
}
