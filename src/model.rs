use crate::solver::SatSolver;
use aig::Aig;
use logic_form::{Clause, Cnf, Cube, Lit, LitMap, Var};
use minisat::SimpSolver;
use satif::Satif;
use std::collections::HashMap;

pub struct Model {
    pub inputs: Vec<Var>,
    pub latchs: Vec<Var>,
    pub primes: Vec<Lit>,
    pub init: Cube,
    pub bad: Cube,
    pub init_map: HashMap<Var, bool>,
    pub constraints: Vec<Lit>,
    pub trans: Cnf,
    num_var: usize,
    next_map: LitMap<Lit>,
    pub max_latch: Var,
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
        let latchs: Vec<Var> = aig.latchs.iter().map(|x| Var::new(x.input)).collect();
        let max_latch = *latchs.iter().max().unwrap();
        let primes: Vec<Lit> = aig.latchs.iter().map(|l| l.next.to_lit()).collect();
        let init = aig.latch_init_cube().to_cube();
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
        for v in inputs.iter().chain(latchs.iter()) {
            simp_solver.set_frozen(*v, true);
        }
        for l in constraints.iter().chain(primes.iter()) {
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
        let trans = aig.get_cnf(&logic);
        let bad_lit = aig_bad.to_lit();
        let bad = Cube::from([bad_lit]);
        simp_solver.set_frozen(bad_lit.var(), true);
        for tran in trans.iter() {
            simp_solver.add_clause(tran);
        }
        for c in constraints.iter() {
            simp_solver.add_clause(&Clause::from([*c]));
        }
        simp_solver.eliminate(true);
        let num_var = simp_solver.num_var();
        let trans = simp_solver.clauses();
        let mut next_map = LitMap::new();
        for (l, p) in latchs.iter().zip(primes.iter()) {
            next_map.reserve(*l);
            let l = l.lit();
            next_map[l] = *p;
            next_map[!l] = !*p;
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
            max_latch,
        }
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit) -> Lit {
        self.next_map[lit]
    }

    #[inline]
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

    pub fn load_trans(&self, solver: &mut SatSolver) {
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
