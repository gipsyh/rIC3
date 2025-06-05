use super::{Transys, TransysIf};
use logic_form::{Lit, LitVec, Var};

impl Transys {
    pub fn merge(&mut self, other: &Self) {
        let offset = self.max_var();
        let map = |x: Var| {
            if x == Var::CONST { x } else { x + offset }
        };
        self.new_var_to(map(other.max_var()));
        let lmap = |x: Lit| Lit::new(map(x.var()), x.polarity());
        for v in Var(1)..=other.max_var() {
            let rel: Vec<LitVec> = other.rel[v]
                .iter()
                .map(|cls| cls.iter().map(|l| lmap(*l)).collect())
                .collect();
            let mv = map(v);
            self.rel.add_rel(mv, &rel);
        }
        for i in other.input.iter() {
            self.input.push(map(*i));
        }
        for &l in other.latch.iter() {
            let ml = map(l);
            self.latch.push(ml);
            self.next.insert(ml, lmap(other.next[&l]));
            if let Some(i) = other.init.get(&l) {
                self.init.insert(ml, *i);
            }
        }
        let mut bad = self.bad.clone();
        bad.extend(other.bad.map(lmap));
        self.bad = LitVec::from(self.rel.new_or(bad));
        for &l in other.constraint.iter() {
            self.constraint.push(lmap(l));
        }
    }
}
