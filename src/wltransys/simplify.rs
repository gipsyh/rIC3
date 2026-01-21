use super::WlTransys;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{Term, TermType};
use std::{mem::take, ops::Deref};

impl WlTransys {
    pub fn coi_refine(&mut self) {
        let mut queue: Vec<_> = self
            .constraint
            .iter()
            .chain(self.bad.iter())
            .chain(self.justice.iter())
            .cloned()
            .collect();
        for l in self.latch.iter() {
            if let Some(init) = self.init.get(l)
                && !init.is_const()
            {
                queue.push(init.clone());
                queue.push(l.clone());
            }
        }
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
        for x in take(&mut self.input) {
            if touch.contains(&x) {
                self.input.push(x);
            }
        }
        for x in take(&mut self.latch) {
            if touch.contains(&x) {
                self.latch.push(x);
            }
        }
        self.init.retain(|k, _| touch.contains(k));
        self.next.retain(|k, _| touch.contains(k));
    }

    pub fn simplify(&mut self) {
        let mut map = GHashMap::new();
        for (_, n) in self.next.iter_mut() {
            *n = n.simplify(&mut map);
        }
        for c in self.constraint.iter_mut() {
            *c = c.simplify(&mut map);
        }
        for b in self.bad.iter_mut() {
            *b = b.simplify(&mut map);
        }
    }
}
