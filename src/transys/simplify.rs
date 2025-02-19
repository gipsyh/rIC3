use super::Transys;
use giputils::hash::{GHashMap, GHashSet};
use logic_form::{Lit, LitMap, LitVec, Var, VarMap};
use minisat::SimpSolver;
use satif::Satif;

impl Transys {
    fn compress_deps_rec(
        v: Var,
        deps: &mut VarMap<Vec<Var>>,
        domain: &GHashSet<Var>,
        compressed: &mut GHashSet<Var>,
    ) {
        if compressed.contains(&v) {
            return;
        }
        for d in 0..deps[v].len() {
            Self::compress_deps_rec(deps[v][d], deps, domain, compressed);
        }
        let mut dep = GHashSet::new();
        for d in deps[v].iter() {
            if domain.contains(d) {
                dep.insert(*d);
                continue;
            }
            for dd in deps[*d].iter() {
                dep.insert(*dd);
            }
        }
        deps[v] = dep.into_iter().collect();
        deps[v].sort();
        compressed.insert(v);
    }

    fn compress_deps(mut deps: VarMap<Vec<Var>>, domain: &GHashSet<Var>) -> VarMap<Vec<Var>> {
        let mut compressed: GHashSet<Var> = GHashSet::new();
        for v in 0..deps.len() {
            let v = Var::new(v);
            Self::compress_deps_rec(v, &mut deps, domain, &mut compressed)
        }
        for v in 0..deps.len() {
            let v = Var::new(v);
            if !domain.contains(&v) {
                deps[v].clear();
            }
        }
        deps
    }

    pub fn simplify(&self, lemmas: &[LitVec], keep_dep: bool, assert_constrain: bool) -> Self {
        let mut simp_solver: Box<dyn Satif> = if keep_dep {
            Box::new(SimpSolver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
        let false_lit: Lit = simp_solver.new_var().into();
        simp_solver.add_clause(&[!false_lit]);
        simp_solver.new_var_to(self.max_var);
        for c in self.trans.iter().chain(lemmas.iter()) {
            simp_solver.add_clause(c);
        }
        let mut frozens = Vec::new();
        for i in self.inputs.iter() {
            frozens.push(*i);
        }
        for l in self.latchs.iter() {
            frozens.push(*l);
            frozens.push(self.var_next(*l))
        }
        frozens.push(self.bad.var());
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
        trans.push(LitVec::from([!false_lit]));
        let mut max_var = false_lit.var();
        let mut domain = GHashSet::from_iter(frozens);
        max_var = *domain.iter().max().unwrap_or(&max_var);
        for cls in trans.iter() {
            for l in cls.iter() {
                domain.insert(l.var());
            }
        }
        max_var = *domain.iter().max().unwrap_or(&max_var);
        for l in self.latchs.iter().chain(self.inputs.iter()) {
            domain.insert(*l);
        }
        let dep = Self::compress_deps(self.dependence.clone(), &domain);
        let mut domain = Vec::from_iter(domain);
        domain.sort();
        let mut domain_map = GHashMap::new();
        for (i, d) in domain.iter().enumerate() {
            domain_map.insert(*d, Var::new(i));
        }
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
        for c in trans.iter_mut() {
            *c = c.iter().map(map_lit).collect();
        }
        let max_var = domain_map[&max_var];
        let mut next_map = LitMap::new_with(max_var);
        let mut prev_map = LitMap::new_with(max_var);
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
        let mut dependence = VarMap::new();
        for d in domain.iter() {
            let dep = dep[*d].clone();
            let dep: Vec<Var> = dep.into_iter().map(|v| domain_map[&v]).collect();
            dependence.push(dep);
        }
        let mut is_latch = VarMap::new_with(max_var);
        for l in latchs.iter() {
            is_latch[*l] = true;
        }
        let mut restore = GHashMap::new();
        for d in domain.iter() {
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
            trans,
            max_var,
            is_latch,
            next_map,
            prev_map,
            dependence,
            max_latch,
            restore,
        }
    }
}
