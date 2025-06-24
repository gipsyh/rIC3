use crate::{
    gipsat::{DagCnfSolver, SolverStatistic},
    transys::{TransysCtx, TransysIf},
};
use giputils::grc::Grc;
use log::error;
use logicrs::{Lit, LitVec, Var, satif::Satif};
use rand::{SeedableRng, rngs::StdRng, seq::SliceRandom};

#[derive(Clone)]
pub struct TransysSolver {
    pub dcs: DagCnfSolver,
    ts: Grc<TransysCtx>,

    relind: LitVec,
    rng: StdRng,
}

impl TransysSolver {
    pub fn new(ts: &Grc<TransysCtx>, assert_cst: bool, rseed: u64) -> Self {
        let mut dcs = DagCnfSolver::new(&ts.rel, rseed);
        if assert_cst {
            for c in ts.constraint.iter() {
                dcs.add_clause(&[*c]);
            }
        }
        Self {
            dcs,
            ts: ts.clone(),
            relind: Default::default(),
            rng: StdRng::seed_from_u64(rseed),
        }
    }

    #[inline]
    pub fn get_assump(&self) -> &LitVec {
        &self.dcs.assump
    }

    pub fn get_pred(
        &mut self,
        solver: &impl Satif,
        target: &[Lit],
        strengthen: bool,
    ) -> (LitVec, LitVec) {
        let mut cls: LitVec = target.into();
        cls.extend_from_slice(&self.ts.constraint);
        if cls.is_empty() {
            return (LitVec::new(), LitVec::new());
        }
        let cls = !cls;
        let mut inputs = LitVec::new();
        for input in self.ts.input.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        self.dcs.set_domain(cls.iter().cloned());
        let mut latchs = LitVec::new();
        for latch in self.ts.latch.iter() {
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
            if let Some(n) = self.dcs.minimal_premise(&inputs, &latchs, &cls) {
                latchs = n;
            } else {
                let fail = target
                    .iter()
                    .chain(self.ts.constraint.iter())
                    .find(|l| !self.sat_value(**l).unwrap())
                    .unwrap();
                error!("assert {fail} failed in lift, please report this bug");
                panic!();
            };
            if latchs.len() == olen || !strengthen {
                break;
            }
        }
        self.dcs.unset_domain();
        (latchs, inputs)
    }

    pub fn trivial_pred(&mut self) -> (LitVec, LitVec) {
        let mut input = LitVec::new();
        for i in self.ts.input() {
            if let Some(v) = self.dcs.sat_value_lit(i) {
                input.push(v);
            }
        }
        let mut latch = LitVec::new();
        for l in self.ts.latch() {
            if let Some(v) = self.dcs.sat_value_lit(l) {
                latch.push(v);
            }
        }
        (input, latch)
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

    pub fn inductive_core(&mut self) -> Option<LitVec> {
        let mut ans = LitVec::new();
        for &l in self.relind.iter() {
            if let Some(nl) = self.ts.next(l)
                && self.dcs.unsat_has(nl)
            {
                ans.push(l);
            }
        }
        if self.ts.cube_subsume_init(&ans) {
            ans = LitVec::new();
            let new = self.relind.iter().find(|&&l| {
                self.ts.init_map[l.var()]
                    .and_then(|l| l.try_constant())
                    .is_some_and(|i| i != l.polarity())
            })?;
            for &l in self.relind.iter() {
                if let Some(nl) = self.ts.next(l)
                    && (self.dcs.unsat_has(nl))
                {
                    ans.push(l);
                }
                if l.eq(new) {
                    ans.push(l);
                }
            }
            assert!(!self.ts.cube_subsume_init(&ans));
        }
        Some(ans)
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
    fn add_clause(&mut self, clause: &[Lit]) {
        self.dcs.add_clause(clause);
    }

    #[inline]
    fn solve(&mut self, assumps: &[Lit]) -> bool {
        self.dcs.solve(assumps)
    }

    #[inline]
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
