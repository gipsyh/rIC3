use super::WlTransys;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{Term, TermType};
use std::ops::Deref;

impl WlTransys {
    pub fn coi_refine(&mut self) {
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
        self.input.retain(|x| touch.contains(x));
        self.latch.retain(|x| touch.contains(x));
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
