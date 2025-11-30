use crate::wltransys::WlTransys;
use giputils::hash::GHashMap;
use logicrs::fol::Term;

#[derive(Clone)]
pub struct WlTransysUnroll {
    pub ts: WlTransys,
    pub num_unroll: usize,
    next_map: GHashMap<Term, Vec<Term>>,
}

impl WlTransysUnroll {
    pub fn new(ts: WlTransys) -> Self {
        let mut next_map = GHashMap::new();
        for t in ts
            .input
            .iter()
            .chain(ts.latch.iter())
            .chain(ts.bad.iter())
            .chain(ts.init.values())
            .chain(ts.next.values())
            .chain(ts.constraint.iter())
            .chain(ts.justice.iter())
        {
            next_map.insert(t.clone(), vec![t.clone()]);
        }
        Self {
            next_map,
            ts,
            num_unroll: 0,
        }
    }

    pub fn unroll(&mut self) {
        let mut ilmap = GHashMap::new();
        for i in self.ts.input.iter() {
            let ni = Term::new_var(i.sort());
            self.next_map.get_mut(i).unwrap().push(ni.clone());
            ilmap.insert(self.next(i, self.num_unroll), ni);
        }
        for l in self.ts.latch.iter() {
            let nl = self.ts.next(l);
            let nl = self.next(&nl, self.num_unroll);
            self.next_map.get_mut(l).unwrap().push(nl.clone());
            ilmap.insert(self.next(l, self.num_unroll), nl);
        }
        let mut cache = GHashMap::new();
        for (_, n) in self.next_map.iter_mut() {
            if n.len() == self.num_unroll + 2 {
                continue;
            }
            let nt = &n[self.num_unroll];
            n.push(nt.cached_apply(&|t| ilmap.get(t).cloned(), &mut cache));
        }
        self.num_unroll += 1;
    }

    pub fn unroll_to(&mut self, k: usize) {
        while self.num_unroll < k {
            self.unroll()
        }
    }

    pub fn next(&self, t: &Term, k: usize) -> Term {
        self.next_map.get(t).unwrap()[k].clone()
    }
}
