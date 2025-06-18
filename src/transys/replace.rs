use crate::transys::Transys;
use logicrs::{VarLMap, VarVMap};

impl Transys {
    pub fn replace(&mut self, map: &VarLMap, rst: &mut VarVMap) {
        for &v in self.input.iter().chain(self.latch.iter()) {
            assert!(!map.contains_key(&v));
        }
        self.rel.replace(map);
        for n in self.next.values_mut() {
            if let Some(m) = map.map_lit(*n) {
                *n = m;
            }
        }
        let map_fn = map.try_map_fn();
        self.bad = self.bad.map(|l| map_fn(l).unwrap_or(l));
        self.constraint = self.constraint.map(|l| map_fn(l).unwrap_or(l));
        self.justice = self.justice.map(|l| map_fn(l).unwrap_or(l));
        rst.retain(|k, _| !map.contains_key(k));
    }
}
