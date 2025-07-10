use crate::transys::Transys;
use giputils::hash::GHashSet;
use log::info;
use logicrs::{LitOrdVec, LitVec, LitVvec, Var, VarMap, VarVMap};

impl Transys {
    pub fn refactor(&self, rst: &mut VarVMap) -> Self {
        let (mut rel, m) = self.rel.topsort();
        let o = rel.num_clause();
        *rst = m.product(rst);
        let mut dep: VarMap<GHashSet<Var>> = VarMap::new_with(rel.max_var());
        for v in rel.var_iter_woc() {
            dep[v] = GHashSet::from_iter(rel.dep(v).iter().copied());
        }
        for x in rel.var_iter_woc() {
            if rel.is_leaf(x) {
                continue;
            }
            let pivot: Vec<_> = rel[x]
                .iter()
                .map(|c| {
                    let mut c = c.clone();
                    let p = c.pop().unwrap();
                    (LitOrdVec::new(c), p)
                })
                .collect();
            'yl: for y in x + 1..=rel.max_var() {
                if rel.is_leaf(y) || !dep[x].is_subset(&dep[y]) {
                    continue;
                }
                let mut refactor = LitVvec::new();
                for r in rel[y].iter() {
                    if !r.iter().any(|l| dep[x].contains(&l.var())) {
                        refactor.push(r.clone());
                        continue;
                    }
                    let r_ov = LitOrdVec::new(r.clone());
                    let Some((c, p)) = pivot.iter().find(|(c, _)| c.subsume(&r_ov)) else {
                        continue 'yl;
                    };
                    let mut r_ov: LitVec =
                        r_ov.iter().copied().filter(|l| !c.contains(l)).collect();
                    r_ov.push(!*p);
                    refactor.push(r_ov);
                }
                refactor.iter().all(|c| c.last().var() == y);
                refactor.subsume_simplify();
                refactor.retain(|c| c.last().var() == y);
                rel.set_rel(y, &refactor);
                dep[y] = GHashSet::from_iter(rel.dep(y).iter().copied());
            }
        }
        info!("refactor ts from {o} to {} clauses", rel.num_clause());
        todo!()
    }
}
