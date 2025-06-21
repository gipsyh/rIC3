use super::WlTransys;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{Term, TermType};
use std::{mem::take, ops::Deref};

impl WlTransys {
    pub fn coi_refine(&mut self, rst: &mut GHashMap<Term, Term>) {
        let mut queue: Vec<_> = self
            .constraint
            .iter()
            .chain(self.bad.iter())
            .chain(self.justice.iter())
            .cloned()
            .collect();
        let mut touch: GHashSet<Term> = GHashSet::from_iter(queue.iter().cloned());
        while let Some(t) = queue.pop() {
            match &t.deref() {
                TermType::Const(_) => (),
                TermType::Var(_) => {
                    if let Some(n) = self.next.get(&t)
                        && touch.insert(n.clone())
                    {
                        queue.push(n.clone());
                    }
                    if let Some(i) = self.init.get(&t)
                        && touch.insert(i.clone())
                    {
                        queue.push(i.clone());
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
        let mut nrst = GHashMap::new();
        for x in take(&mut self.input) {
            if touch.contains(&x) {
                nrst.insert(x.clone(), rst[&x].clone());
                self.input.push(x);
            }
        }
        for x in take(&mut self.latch) {
            if touch.contains(&x) {
                nrst.insert(x.clone(), rst[&x].clone());
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
        for b in self.bad.iter_mut() {
            *b = b.simplify(&mut self.tm, &mut map);
        }
    }
}
