use crate::{
    gipsat::{DagCnfSolver, SolverStatistic},
    transys::{TransysCtx, TransysIf},
};
use giputils::grc::Grc;
use logic_form::{Lit, LitVec, Var};
use rand::{SeedableRng, rngs::StdRng, seq::SliceRandom};
use satif::Satif;

pub struct TransysSolver {
    dcs: DagCnfSolver,
    _id: Option<usize>,
    ts: Grc<TransysCtx>,

    relind: LitVec,
    rng: StdRng,
}

impl TransysSolver {
    pub fn new(id: Option<usize>, ts: &Grc<TransysCtx>, rseed: u64) -> Self {
        let mut dcs = DagCnfSolver::new(&ts.rel, rseed);
        if id.is_some() {
            for c in ts.constraints.iter() {
                dcs.add_clause(&[*c]);
            }
        }
        dcs.simplify_satisfied();
        Self {
            _id: id,
            dcs,
            ts: ts.clone(),
            relind: Default::default(),
            rng: StdRng::seed_from_u64(rseed),
        }
    }

    #[inline]
    pub fn add_lemma(&mut self, lemma: &[Lit]) {
        self.dcs.add_clause(lemma);
    }

    #[inline]
    pub fn solve_without_bucket(&mut self, assump: &[Lit], constraint: Vec<LitVec>) -> bool {
        self.dcs.solve_without_bucket(assump, constraint)
    }

    #[inline]
    pub fn minimal_pred(
        &mut self,
        inputs: &[Lit],
        latchs: &[Lit],
        target_constrain: &LitVec,
    ) -> Option<LitVec> {
        let assump = LitVec::from_iter(inputs.iter().chain(latchs.iter()).copied());
        if self
            .dcs
            .solve_with_constraint(&assump, vec![target_constrain.clone()])
        {
            return None;
        }
        Some(
            latchs
                .iter()
                .filter(|l| self.dcs.unsat_has(**l))
                .copied()
                .collect(),
        )
    }

    #[inline]
    pub fn get_assump(&self) -> &LitVec {
        &self.dcs.assump
    }

    #[allow(unused)]
    pub fn get_pred(
        &mut self,
        solver: &impl Satif,
        target: &[Lit],
        strengthen: bool,
    ) -> (LitVec, LitVec) {
        let mut cls: LitVec = target.into();
        cls.extend_from_slice(&self.ts.constraints);
        if cls.is_empty() {
            return (LitVec::new(), LitVec::new());
        }
        let cls = !cls;
        let mut inputs = LitVec::new();
        for input in self.ts.inputs.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        self.dcs.set_domain(cls.iter().cloned());
        let mut latchs = LitVec::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            if self.dcs.domain.has(lit.var())
                && let Some(v) = solver.sat_value(lit)
            {
                latchs.push(lit.not_if(!v));
            }
        }
        for _ in 0.. {
            if latchs.is_empty() {
                break;
            }
            latchs.shuffle(&mut self.rng);
            let olen = latchs.len();
            latchs = self.minimal_pred(&inputs, &latchs, &cls).unwrap();
            if latchs.len() == olen || !strengthen {
                break;
            }
        }
        self.dcs.unset_domain();
        (latchs, inputs)
    }

    #[allow(unused)]
    pub fn trivial_pred(&mut self) -> LitVec {
        let mut latchs = LitVec::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            if let Some(v) = self.dcs.sat_value(lit) {
                // if !self.flip_to_none(*latch) {
                latchs.push(lit.not_if(!v));
                // }
            }
        }
        latchs
    }

    pub fn inductive_with_constrain(
        &mut self,
        cube: &[Lit],
        strengthen: bool,
        mut constraint: Vec<LitVec>,
    ) -> bool {
        self.relind = LitVec::from(cube);
        let assump = self.ts.lits_next(cube);
        if strengthen {
            constraint.push(LitVec::from_iter(cube.iter().map(|l| !*l)));
        }
        !self.dcs.solve_with_constraint(&assump, constraint.clone())
    }

    pub fn inductive(&mut self, cube: &[Lit], strengthen: bool) -> bool {
        self.inductive_with_constrain(cube, strengthen, vec![])
    }

    pub fn inductive_core(&mut self) -> LitVec {
        let mut ans = LitVec::new();
        for &l in self.relind.iter() {
            let nl = self.ts.next(l);
            if self.dcs.unsat_has(nl) {
                ans.push(l);
            }
        }
        if self.ts.cube_subsume_init(&ans) {
            ans = LitVec::new();
            let new = self
                .relind
                .iter()
                .find(|&&l| self.ts.init_map[l.var()].is_some_and(|i| i != l.polarity()))
                .unwrap();
            for &l in self.relind.iter() {
                let nl = self.ts.next(l);
                if self.dcs.unsat_has(nl) || l.eq(new) {
                    ans.push(l);
                }
            }
            assert!(!self.ts.cube_subsume_init(&ans));
        }
        ans
    }

    #[inline]
    pub fn flip_to_none(&mut self, var: Var) -> bool {
        self.dcs.flip_to_none(var)
    }

    #[inline]
    pub fn domain_has(&self, var: Var) -> bool {
        self.dcs.domain_has(var)
    }

    #[inline]
    pub fn set_domain(&mut self, domain: impl IntoIterator<Item = Lit>) {
        self.dcs.set_domain(domain);
    }

    #[inline]
    pub fn unset_domain(&mut self) {
        self.dcs.unset_domain();
    }

    #[inline]
    pub fn add_domain(&mut self, var: Var, deps: bool) {
        self.dcs.add_domain(var, deps);
    }

    #[inline]
    pub fn statistic(&self) -> &SolverStatistic {
        self.dcs.statistic()
    }
}

impl Satif for TransysSolver {
    #[inline]
    fn new_var(&mut self) -> Var {
        self.dcs.new_var()
    }

    #[inline]
    fn num_var(&self) -> usize {
        self.dcs.num_var()
    }

    #[inline]
    fn add_clause(&mut self, _clause: &[Lit]) {
        todo!();
        // self.dcs.add_clause(clause);
    }

    #[inline]
    fn solve(&mut self, assumps: &[Lit]) -> bool {
        self.dcs.solve(assumps)
    }

    fn solve_with_constraint(&mut self, assumps: &[Lit], constraint: Vec<LitVec>) -> bool {
        self.dcs.solve_with_constraint(assumps, constraint)
    }

    #[inline]
    fn sat_value(&self, lit: Lit) -> Option<bool> {
        self.dcs.sat_value(lit)
    }

    #[inline]
    fn unsat_has(&self, lit: Lit) -> bool {
        self.dcs.unsat_has(lit)
    }
}
