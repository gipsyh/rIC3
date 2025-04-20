use super::{Transys, TransysIf};
use giputils::hash::GHashMap;
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
        let bad = self.rel.new_or([self.bad, lmap(other.bad)]);
        self.bad = bad;
        for &l in other.constraint.iter() {
            self.constraint.push(lmap(l));
        }
    }

    pub fn reencode(&mut self) {
        let mut res = Self::new();
        let mut encode_map = GHashMap::new();
        encode_map.insert(Var::CONST, Var::CONST);
        for f in self.input.iter() {
            let t = res.new_var();
            encode_map.insert(*f, t);
        }
        for f in self.latch.iter() {
            let t = res.new_var();
            encode_map.insert(*f, t);
        }
        for (f, _) in self.rel.iter() {
            encode_map.entry(f).or_insert_with(|| res.new_var());
        }
        res.rel = self.rel.map(|v| encode_map[&v]);
        for l in self.input.iter() {
            res.input.push(encode_map[l]);
        }
        for l in self.latch.iter() {
            let ml = encode_map[l];
            res.latch.push(ml);
            res.next
                .insert(ml, self.next[l].map_var(|v| encode_map[&v]));
            if let Some(i) = self.init.get(l) {
                res.init.insert(ml, *i);
            }
        }
        res.bad = self.bad.map_var(|v| encode_map[&v]);
        res.constraint = self.constraint.map(|l| l.map_var(|v| encode_map[&v]));
        for (f, t) in self.rst.iter() {
            res.rst.insert(encode_map[f], encode_map[t]);
        }
        *self = res;
    }
}
