use super::{Transys, TransysIf};
use giputils::hash::GHashSet;
use logic_form::{Lit, Var, VarVMap};
use std::mem::take;

impl Transys {
    pub fn coi_refine(&mut self, rst: &mut VarVMap) {
        let mut mark = GHashSet::new();
        let mut queue = Vec::new();
        for v in self
            .constraint
            .iter()
            .chain(self.bad.iter())
            .chain(self.justice.iter())
            .map(|l| l.var())
        {
            if !mark.contains(&v) {
                mark.insert(v);
                queue.push(v);
            }
        }
        if !self.justice.is_empty() {
            for v in self.latch.iter() {
                if !mark.contains(v) {
                    mark.insert(*v);
                    queue.push(*v);
                }
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
            for &d in self.rel.dep(v).iter() {
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
                rst.remove(&v);
            }
        }
    }

    pub fn rearrange(&mut self, rst: &mut VarVMap) {
        let mut additional = vec![Var::CONST];
        additional.extend_from_slice(&self.input);
        additional.extend(
            self.constraint
                .iter()
                .chain(self.bad.iter())
                .chain(self.justice.iter())
                .map(|l| l.var()),
        );
        for l in self.latch.iter() {
            additional.push(*l);
            additional.push(self.next[l].var());
        }
        let domain_map = self.rel.rearrange(additional.into_iter());
        let map_lit = |l: Lit| Lit::new(domain_map[l.var()], l.polarity());
        self.input = self.input.iter().map(|v| domain_map[*v]).collect();
        self.latch = self.latch.iter().map(|v| domain_map[*v]).collect();
        self.init = self
            .init
            .iter()
            .map(|(v, i)| (domain_map[*v], *i))
            .collect();
        self.next = self
            .next
            .iter()
            .map(|(v, &n)| (domain_map[*v], map_lit(n)))
            .collect();
        self.bad = self.bad.map(map_lit);
        self.constraint = self.constraint.map(map_lit);
        self.justice = self.justice.map(map_lit);
        *rst = domain_map.inverse().product(rst);
    }

    pub fn simplify(&mut self, rst: &mut VarVMap) {
        self.coi_refine(rst);
        let mut frozens = vec![Var::CONST];
        frozens.extend(
            self.bad
                .iter()
                .chain(self.constraint.iter())
                .chain(self.justice.iter())
                .map(|l| l.var()),
        );
        frozens.extend_from_slice(&self.input);
        for l in self.latch.iter() {
            frozens.push(*l);
            frozens.push(self.next[l].var());
        }
        self.rel = self.rel.simplify(frozens.iter().copied());
        self.rearrange(rst);
    }
}
