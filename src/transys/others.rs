use super::{Transys, TransysIf};
use giputils::hash::GHashMap;
use logicrs::{Lit, LitVec, Var, satif::Satif};

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
                self.init.insert(ml, lmap(*i));
            }
        }
        let mut bad = self.bad.clone();
        bad.extend(other.bad.map(lmap));
        self.bad = LitVec::from(self.rel.new_or(bad));
        for &l in other.constraint.iter() {
            self.constraint.push(lmap(l));
        }
        for &l in other.justice.iter() {
            self.justice.push(lmap(l));
        }
    }

    pub fn exact_init_state(&self, assump: &[Lit]) -> (LitVec, LitVec) {
        let mut solver = cadical::Solver::new();
        self.load_init(&mut solver);
        self.load_trans(&mut solver, true);
        assert!(solver.solve(assump));
        let mut state = LitVec::new();
        for l in self.latch() {
            state.push(solver.sat_value_lit(l).unwrap());
        }
        let mut input = LitVec::new();
        for i in self.input() {
            input.push(solver.sat_value_lit(i).unwrap());
        }
        (input, state)
    }

    pub fn remove_gate_init(&self) -> Self {
        let mut res = self.clone();
        let mut init = GHashMap::new();
        let mut eq = Vec::new();
        for l in self.input().chain(self.latch()) {
            if let Some(i) = self.init.get(&l).copied() {
                if i.try_constant().is_some() {
                    init.insert(l, i);
                } else {
                    eq.push((l, i));
                }
            }
        }
        if eq.is_empty() {
            return res;
        }
        res.init = init;
        let iv = res.new_var();
        res.add_latch(iv, Some(Lit::constant(true)), Lit::constant(false));
        for (v, i) in eq {
            let e = res.rel.new_xnor(v.lit(), i);
            let c = res.rel.new_imply(iv.lit(), e);
            res.constraint.push(c);
        }
        res
    }
}
