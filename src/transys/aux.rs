use crate::transys::{Transys, TransysIf};
use giputils::hash::{GHashMap, GHashSet};
use logicrs::{DagCnf, Var, VarRange};

impl Transys {
    pub fn add_aux(&mut self, rel: &DagCnf, auxs: &GHashSet<Var>) {
        let vars = VarRange::new_inclusive(self.max_var() + 1, rel.max_var());
        let mut next = GHashMap::new();
        for v in vars.clone() {
            self.rel.add_rel(v, &rel[v]);
        }
        for v in vars {
            let n = self.rel.new_var();
            next.insert(v, n);
            let mut ncls = Vec::new();
            for cls in self.rel[n].iter() {
                ncls.push(
                    cls.iter()
                        .map(|l| {
                            self.next
                                .get(&l.var())
                                .copied()
                                .unwrap_or(next[&l.var()].lit())
                                .not_if(!l.polarity())
                        })
                        .collect(),
                );
            }
            self.rel.add_rel(n, &ncls);
        }
        for v in auxs.iter() {
            self.add_latch(*v, None, next[v].lit());
        }
    }
}
