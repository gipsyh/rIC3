use aig::Aig;
use cadical::Solver;
use logic_form::{Clause, Cnf, Cube, Lit, Var};
use minisat::SimpSolver;
use satif::Satif;
use std::collections::HashMap;

pub struct Model {
    pub inputs: Vec<Var>,
    pub latchs: Vec<Var>,
    pub primes: Vec<Var>,
    pub init: Cube,
    pub bad: Cube,
    pub init_map: HashMap<Var, bool>,
    pub constraints: Vec<Lit>,
    pub trans: Cnf,
    num_var: usize,
    next_map: HashMap<Var, Var>,
    previous_map: HashMap<Var, Var>,
}

impl Model {
    pub fn from_aig(aig: &Aig) -> Self {
        let mut simp_solver = SimpSolver::new();
        let false_lit: Lit = simp_solver.new_var().into();
        simp_solver.add_clause(&[!false_lit]);
        for node in aig.nodes.iter().skip(1) {
            assert_eq!(Var::new(node.node_id()), simp_solver.new_var());
        }
        let inputs: Vec<Var> = aig.inputs.iter().map(|x| Var::new(*x)).collect();
        let mut latchs: Vec<Var> = aig.latchs.iter().map(|x| Var::new(x.input)).collect();
        latchs.push(simp_solver.new_var());
        let primes: Vec<Var> = latchs.iter().map(|_| simp_solver.new_var()).collect();
        let bad_var_lit = latchs.last().unwrap().lit();
        let bad_var_prime_lit = primes.last().unwrap().lit();
        let mut init = aig.latch_init_cube().to_cube();
        init.push(!bad_var_lit);
        let mut init_map = HashMap::new();
        for l in init.iter() {
            init_map.insert(l.var(), l.polarity());
        }
        let constraints: Vec<Lit> = aig.constraints.iter().map(|c| c.to_lit()).collect();
        assert!(constraints.is_empty());
        let aig_bad = if aig.bads.is_empty() {
            aig.outputs[0]
        } else {
            aig.bads[0]
        };
        for v in inputs.iter().chain(latchs.iter()).chain(primes.iter()) {
            simp_solver.set_frozen(*v, true);
        }
        for l in constraints.iter() {
            simp_solver.set_frozen(l.var(), true);
        }
        let mut logic = Vec::new();
        for l in aig.latchs.iter() {
            logic.push(l.next);
        }
        for c in aig.constraints.iter() {
            logic.push(*c);
        }
        logic.push(aig_bad);
        let mut trans = aig.get_cnf(&logic);
        let bad_lit = aig_bad.to_lit();
        trans.push(Clause::from([!bad_lit, bad_var_prime_lit]));
        trans.push(Clause::from([bad_lit, !bad_var_prime_lit]));
        let bad = Cube::from([bad_var_prime_lit]);
        for tran in trans.iter() {
            simp_solver.add_clause(tran);
        }
        for (l, p) in aig.latchs.iter().zip(primes.iter()) {
            let l = l.next.to_lit();
            let p = p.lit();
            simp_solver.add_clause(&Clause::from([l, !p]));
            simp_solver.add_clause(&Clause::from([!l, p]));
        }
        for c in constraints.iter() {
            simp_solver.add_clause(&Clause::from([*c]));
        }
        simp_solver.eliminate(true);
        let num_var = simp_solver.num_var();
        let trans = simp_solver.clauses();
        let mut next_map = HashMap::new();
        let mut previous_map = HashMap::new();
        for (l, p) in latchs.iter().zip(primes.iter()) {
            next_map.insert(*l, *p);
            previous_map.insert(*p, *l);
        }
        Self {
            inputs,
            latchs,
            primes,
            init,
            bad,
            init_map,
            constraints,
            trans,
            num_var,
            next_map,
            previous_map,
        }
    }

    #[inline]
    pub fn lit_previous(&self, lit: Lit) -> Lit {
        Lit::new(self.previous_map[&lit.var()], lit.polarity())
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit) -> Lit {
        Lit::new(self.next_map[&lit.var()], lit.polarity())
    }

    pub fn cube_previous(&self, cube: &Cube) -> Cube {
        cube.iter().map(|l| self.lit_previous(*l)).collect()
    }

    pub fn cube_next(&self, cube: &Cube) -> Cube {
        cube.iter().map(|l| self.lit_next(*l)).collect()
    }

    pub fn cube_subsume_init(&self, x: &Cube) -> bool {
        for i in 0..x.len() {
            if let Some(init) = self.init_map.get(&x[i].var()) {
                if *init != x[i].polarity() {
                    return false;
                }
            }
        }
        true
    }

    pub fn load_trans(&self, solver: &mut Solver) {
        while solver.num_var() < self.num_var {
            solver.new_var();
        }
        for cls in self.trans.iter() {
            solver.add_clause(cls)
        }
    }

    pub fn inits(&self) -> Vec<Cube> {
        self.init_map
            .iter()
            .map(|(latch, init)| Cube::from([Lit::new(*latch, !init)]))
            .collect()
    }
}
