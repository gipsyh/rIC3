use super::builder::TransysBuilder;
use logic_form::{Lit, LitVec, Var};
use minisat::SimpSolver;
use satif::Satif;

impl TransysBuilder {
    pub fn simplify(&mut self, keep_dep: bool, assert_constrain: bool) {
        let mut simp_solver: Box<dyn Satif> = if keep_dep {
            Box::new(SimpSolver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
        simp_solver.new_var_to(self.rel.max_var());
        for c in self.rel.iter() {
            simp_solver.add_clause(c);
        }
        let mut frozens = vec![Var::CONST, self.bad.var()];
        frozens.extend_from_slice(&self.input);
        for l in self.latch.iter() {
            frozens.push(*l);
            frozens.push(self.next[l].var());
        }
        for c in self.constraint.iter() {
            if assert_constrain {
                simp_solver.add_clause(&[*c]);
            } else {
                frozens.push(c.var());
            }
        }
        for f in frozens.iter() {
            simp_solver.set_frozen(*f, true);
        }
        if let Some(false) = simp_solver.simplify() {
            println!("warning: model trans simplified with unsat");
        }
        let mut trans = simp_solver.clauses();
        trans.push(LitVec::from([Lit::constant(true)]));
        unsafe { self.rel.set_cls(trans) };
        let domain_map = self.rel.arrange(frozens.into_iter());
        let map_lit = |l: &Lit| Lit::new(domain_map[&l.var()], l.polarity());
        self.input = self.input.iter().map(|v| domain_map[v]).collect();
        self.latch = self.latch.iter().map(|v| domain_map[v]).collect();
        self.init = self.init.iter().map(|(v, i)| (domain_map[v], *i)).collect();
        self.next = self
            .next
            .iter()
            .map(|(v, n)| (domain_map[v], map_lit(n)))
            .collect();
        self.bad = map_lit(&self.bad);
        self.constraint = if assert_constrain {
            Default::default()
        } else {
            self.constraint.iter().map(map_lit).collect()
        };
        self.rst = self
            .rst
            .iter()
            .filter_map(|(k, &v)| domain_map.get(k).map(|&dk| (dk, v)))
            .collect();
    }
}
