use super::Transys;
use giputils::hash::GHashMap;
use logic_form::{Lit, LitMap, LitVec, Var, VarMap};
use minisat::SimpSolver;
use satif::Satif;

impl Transys {
    pub fn simplify(&self, lemmas: &[LitVec], keep_dep: bool, assert_constrain: bool) -> Self {
        let mut simp_solver: Box<dyn Satif> = if keep_dep {
            Box::new(SimpSolver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
        simp_solver.new_var_to(self.max_var());
        for c in self.rel.iter().chain(lemmas.iter()) {
            simp_solver.add_clause(c);
        }
        let mut frozens = vec![Var::CONST, self.bad.var()];
        frozens.extend_from_slice(&self.inputs);
        for l in self.latchs.iter() {
            frozens.push(*l);
            frozens.push(self.var_next(*l))
        }
        for c in self.constraints.iter() {
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
        let mut rel = self.rel.clone();
        unsafe { rel.set_cls(trans) };
        let domain_map = rel.arrange(frozens.into_iter());
        let map_lit = |l: &Lit| Lit::new(domain_map[&l.var()], l.polarity());
        let inputs = self.inputs.iter().map(|v| domain_map[v]).collect();
        let latchs: Vec<Var> = self.latchs.iter().map(|v| domain_map[v]).collect();
        let init = self.init.iter().map(map_lit).collect();
        let bad = map_lit(&self.bad);
        let max_latch = domain_map[&self.max_latch];
        let mut init_map: VarMap<Option<bool>> = VarMap::new_with(max_latch);
        for l in self.latchs.iter() {
            init_map[domain_map[l]] = self.init_map[*l];
        }
        let constraints = if assert_constrain {
            Default::default()
        } else {
            self.constraints.iter().map(map_lit).collect()
        };
        let mut next_map = LitMap::new_with(rel.max_var());
        let mut prev_map = LitMap::new_with(rel.max_var());
        for l in self.latchs.iter() {
            let l = l.lit();
            let p = self.lit_next(l);
            let l = map_lit(&l);
            let p = map_lit(&p);
            next_map[l] = p;
            next_map[!l] = !p;
            prev_map[p] = l;
            prev_map[!p] = !l;
        }

        let mut is_latch = VarMap::new_with(rel.max_var());
        for l in latchs.iter() {
            is_latch[*l] = true;
        }
        let mut restore = GHashMap::new();
        for d in domain_map.keys() {
            if let Some(r) = self.restore.get(d) {
                restore.insert(domain_map[d], *r);
            }
        }
        Self {
            inputs,
            latchs,
            init,
            bad,
            init_map,
            constraints,
            rel,
            is_latch,
            next_map,
            prev_map,
            max_latch,
            restore,
        }
    }
}
