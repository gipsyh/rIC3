use crate::{
    gipsat::{DagCnfSolver, SolverStatistic},
    transys::{TransysCtx, TransysIf},
};
use giputils::grc::Grc;
use logicrs::{Lit, LitVec, Var, satif::Satif};

#[derive(Clone)]
pub struct TransysSolver {
    pub dcs: DagCnfSolver,
    ts: Grc<TransysCtx>,

    relind: LitVec,
}

impl TransysSolver {
    pub fn new(ts: &Grc<TransysCtx>) -> Self {
        let mut dcs = DagCnfSolver::new(&ts.rel);
        for c in ts.constraint.iter() {
            dcs.add_clause(&[*c]);
        }
        Self {
            dcs,
            ts: ts.clone(),
            relind: Default::default(),
        }
    }

    #[inline]
    pub fn get_assump(&self) -> &LitVec {
        &self.dcs.assump
    }

    #[allow(unused)]
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
            let nl = self.ts.next(l);
            if self.dcs.unsat_has(nl) {
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
                let nl = self.ts.next(l);
                if self.dcs.unsat_has(nl) {
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
    pub fn set_domain(&mut self, domain: impl IntoIterator<Item = Lit>) {
        self.dcs.set_domain(domain);
    }

    #[inline]
    pub fn unset_domain(&mut self) {
        self.dcs.unset_domain();
    }

    #[inline]
    #[allow(unused)]
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

    #[inline]
    fn flip_to_none(&mut self, var: Var) -> bool {
        self.dcs.flip_to_none(var)
    }
}
