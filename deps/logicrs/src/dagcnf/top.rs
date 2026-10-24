use std::cmp::Ordering;

use crate::{DagCnf, LitVec, Var, VarMap, VarVMap};

impl DagCnf {
    pub fn level(&self) -> VarMap<usize> {
        let mut level = VarMap::new_with(self.max_var);
        for v in self.var_iter() {
            level[v] = self.dep[v]
                .iter()
                .map(|&d| level[d])
                .max()
                .map(|l| l + 1)
                .unwrap_or_default();
        }
        level
    }

    pub fn topsort(&self) -> (Self, VarVMap) {
        let mut map = VarVMap::new();
        map.insert(Var::CONST, Var::CONST);
        let mut deps = Vec::new();
        let level = self.level();
        for v in self.var_iter_woc() {
            let mut d: LitVec = self.dep[v].iter().map(|v| v.lit()).collect();
            d.sort();
            deps.push((d, v));
        }
        deps.sort_by(|a, b| match level[a.1].cmp(&level[b.1]) {
            Ordering::Equal => a.0.cmp(&b.0),
            o => o,
        });
        for ((_, d), v) in deps.into_iter().zip(self.var_iter().skip(1)) {
            map.insert(d, v);
        }
        (self.map(|v| map[v]), map.inverse())
    }
}
