use super::{Transys, TransysIf};
use giputils::hash::GHashSet;
use logic_form::{Lit, Var};
use std::mem::take;

impl Transys {
    pub fn coi_refine(&mut self) {
        let mut mark = GHashSet::new();
        let mut queue = Vec::new();
        for v in self
            .constraint
            .iter()
            .chain(self.bad.iter())
            .map(|l| l.var())
        {
            if !mark.contains(&v) {
                mark.insert(v);
                queue.push(v);
            }
        }
        while let Some(v) = queue.pop() {
            if let Some(n) = self.next.get(&v) {
                let nv = n.var();
                if !mark.contains(&nv) {
                    mark.insert(nv);
                    queue.push(nv);
                }
            }
            for &d in self.rel.dep[v].iter() {
                if !mark.contains(&d) {
                    mark.insert(d);
                    queue.push(d);
                }
            }
        }
        self.input.retain(|i| mark.contains(i));
        for l in take(&mut self.latch) {
            if mark.contains(&l) {
                self.latch.push(l);
            } else {
                self.next.remove(&l);
                self.init.remove(&l);
            }
        }
        for v in Var::CONST + 1..=self.max_var() {
            if !mark.contains(&v) {
                self.rel.del_rel(v);
                self.rst.remove(&v);
            }
        }
    }

    pub fn rearrange(&mut self) {
        let mut additional = vec![Var::CONST];
        additional.extend(self.bad.iter().map(|l| l.var()));
        additional.extend_from_slice(&self.input);
        additional.extend(self.constraint.iter().map(|l| l.var()));
        for l in self.latch.iter() {
            additional.push(*l);
            additional.push(self.next[l].var());
        }
        let domain_map = self.rel.rearrange(additional.into_iter());
        let map_lit = |l: Lit| Lit::new(domain_map[&l.var()], l.polarity());
        self.input = self.input.iter().map(|v| domain_map[v]).collect();
        self.latch = self.latch.iter().map(|v| domain_map[v]).collect();
        self.init = self.init.iter().map(|(v, i)| (domain_map[v], *i)).collect();
        self.next = self
            .next
            .iter()
            .map(|(v, &n)| (domain_map[v], map_lit(n)))
            .collect();
        self.bad = self.bad.map(map_lit);
        self.constraint = self.constraint.map(map_lit);
        self.rst = self
            .rst
            .iter()
            .filter_map(|(k, &v)| domain_map.get(k).map(|&dk| (dk, v)))
            .collect();
    }

    pub fn simplify(&mut self) {
        self.coi_refine();
        let mut frozens = vec![Var::CONST];
        frozens.extend(self.bad.iter().map(|l| l.var()));
        frozens.extend_from_slice(&self.input);
        for l in self.latch.iter() {
            frozens.push(*l);
            frozens.push(self.next[l].var());
        }
        for c in self.constraint.iter() {
            frozens.push(c.var());
        }
        self.rel = self.rel.simplify(frozens.iter().copied());
        self.rearrange();
    }
}
