mod analyze;
mod cdb;
mod domain;
mod pred;
mod propagate;
mod search;
mod simplify;
mod statistic;
mod vsids;

use crate::transys::TransysIf;
use crate::{config::Options, transys::TransysCtx};
use analyze::Analyze;
pub use cdb::ClauseKind;
use cdb::{CREF_NONE, CRef, ClauseDB};
use domain::Domain;
use giputils::{grc::Grc, gvec::Gvec};
use logic_form::Lbool;
use logic_form::{Lemma, Lit, LitSet, LitVec, Var, VarMap};
use propagate::Watchers;
use rand::{SeedableRng, rngs::StdRng};
use satif::Satif;
use search::Value;
use simplify::Simplify;
pub use statistic::SolverStatistic;
use vsids::Vsids;

pub struct Solver {
    id: Option<usize>,
    cdb: ClauseDB,
    watchers: Watchers,
    value: Value,
    trail: Gvec<Lit>,
    pos_in_trail: Vec<u32>,
    level: VarMap<u32>,
    reason: VarMap<CRef>,
    propagated: u32,
    vsids: Vsids,
    phase_saving: VarMap<Lbool>,
    analyze: Analyze,
    simplify: Simplify,
    unsat_core: LitSet,
    pub domain: Domain,
    temporary_domain: bool,
    prepared_vsids: bool,
    constrain_act: Var,

    ts: Grc<TransysCtx>,

    assump: LitVec,
    constraint: Vec<LitVec>,

    trivial_unsat: bool,
    mark: LitSet,
    rng: StdRng,
    pub statistic: SolverStatistic,
    #[allow(unused)]
    options: Options,
}

impl Solver {
    pub fn new(options: Options, id: Option<usize>, ts: &Grc<TransysCtx>) -> Self {
        let mut solver = Self {
            id,
            ts: ts.clone(),
            cdb: Default::default(),
            watchers: Default::default(),
            value: Default::default(),
            trail: Default::default(),
            pos_in_trail: Default::default(),
            level: Default::default(),
            reason: Default::default(),
            propagated: Default::default(),
            vsids: Default::default(),
            phase_saving: Default::default(),
            analyze: Default::default(),
            simplify: Default::default(),
            unsat_core: Default::default(),
            domain: Domain::new(),
            temporary_domain: Default::default(),
            prepared_vsids: false,
            constrain_act: Var(0),
            assump: Default::default(),
            constraint: Default::default(),
            statistic: Default::default(),
            trivial_unsat: false,
            rng: StdRng::seed_from_u64(options.rseed),
            mark: Default::default(),
            options,
        };
        while solver.num_var() < solver.ts.num_var() {
            solver.new_var();
        }
        for cls in ts.rel.clause() {
            solver.add_clause_inner(cls, ClauseKind::Trans);
        }
        if solver.id.is_some() {
            for c in ts.constraints.iter() {
                solver.add_clause_inner(&[*c], ClauseKind::Trans);
            }
        }
        if id.is_some() {
            solver.domain.calculate_constrain(&solver.ts, &solver.value);
        }
        assert!(solver.highest_level() == 0);
        if solver.propagate() != CREF_NONE {
            solver.trivial_unsat = true;
            solver.unsat_core.clear();
        }
        solver.simplify_satisfied();
        solver
    }

    #[inline]
    pub fn num_var(&self) -> usize {
        self.constrain_act.into()
    }

    fn simplify_clause(&mut self, cls: &[Lit]) -> Option<logic_form::LitVec> {
        assert!(self.highest_level() == 0);
        let mut clause = logic_form::LitVec::new();
        for l in cls.iter() {
            assert!(l.var() < self.num_var() + 1);
            match self.value.v(*l) {
                Lbool::TRUE => return None,
                Lbool::FALSE => (),
                _ => clause.push(*l),
            }
        }
        Some(clause)
    }

    pub fn add_clause_inner(&mut self, clause: &[Lit], mut kind: ClauseKind) -> CRef {
        let Some(clause) = self.simplify_clause(clause) else {
            return CREF_NONE;
        };
        if clause.is_empty() {
            self.trivial_unsat = true;
            return CREF_NONE;
        }
        for l in clause.iter() {
            if self.constrain_act == l.var() {
                kind = ClauseKind::Temporary;
            }
        }
        if clause.len() == 1 {
            assert!(!matches!(kind, ClauseKind::Temporary));
            match self.value.v(clause[0]) {
                Lbool::TRUE | Lbool::FALSE => todo!(),
                _ => {
                    self.assign(clause[0], CREF_NONE);
                    if self.propagate() != CREF_NONE {
                        self.trivial_unsat = true;
                    }
                    CREF_NONE
                }
            }
        } else {
            self.attach_clause(&clause, kind)
        }
    }

    #[inline]
    pub fn add_lemma(&mut self, lemma: &[Lit]) -> CRef {
        self.reset();
        for l in lemma.iter() {
            self.add_domain(l.var(), true);
        }
        self.add_clause_inner(lemma, ClauseKind::Lemma)
    }

    // #[inline]
    // pub fn remove_lemma(&mut self, lemma: &[Lit]) {
    // self.simplify.lazy_remove.push(LitVec::from(lemma));
    // }

    #[allow(unused)]
    pub fn lemmas(&mut self) -> Vec<Lemma> {
        self.reset();
        let mut lemmas = Vec::new();
        for t in self.trail.iter() {
            if self.ts.is_latch(t.var()) {
                lemmas.push(Lemma::new(LitVec::from([!*t])));
            }
        }
        for l in self.cdb.lemmas.iter() {
            let lemma = LitVec::from_iter(self.cdb.get(*l).slice().iter().map(|l| !*l));
            lemmas.push(Lemma::new(lemma));
        }
        lemmas
    }

    pub fn reset(&mut self) {
        self.backtrack(0, false);
        self.clean_temporary();
        self.prepared_vsids = false;
        self.domain.reset();
        assert!(!self.temporary_domain);
    }

    fn new_round(
        &mut self,
        domain: impl Iterator<Item = Var>,
        constraint: Vec<LitVec>,
        bucket: bool,
    ) -> bool {
        self.backtrack(0, self.temporary_domain);
        self.clean_temporary();
        self.prepared_vsids = false;
        // dbg!(&self.name);
        // self.vsids.activity.print();
        // dbg!(self.num_var());
        // dbg!(self.trail.len());
        // dbg!(self.cdb.num_leanrt());
        // dbg!(self.cdb.num_lemma());

        for mut c in constraint {
            c.push(!self.constrain_act.lit());
            if let Some(c) = self.simplify_clause(&c) {
                assert!(!c.is_empty());
                if c.len() == 1 {
                    return false;
                }
                self.add_clause_inner(&c, ClauseKind::Temporary);
            }
        }

        if !self.temporary_domain {
            self.domain.enable_local(domain, &self.ts, &self.value);
            assert!(!self.domain.has(self.constrain_act));
            self.domain.insert(self.constrain_act);
            if bucket {
                self.vsids.enable_bucket = true;
                self.vsids.bucket.clear();
            } else {
                self.vsids.enable_bucket = false;
                self.vsids.heap.clear();
            }
        }
        self.statistic.avg_decide_var +=
            self.domain.len() as f64 / (self.ts.num_var() - self.trail.len() as usize) as f64;
        true
    }

    fn solve_inner(&mut self, assump: &[Lit], constraint: Vec<LitVec>, bucket: bool) -> bool {
        self.assump = assump.into();
        self.constraint = constraint.clone();
        if self.trivial_unsat {
            self.unsat_core.clear();
            return false;
        }
        assert!(!assump.is_empty());
        self.statistic.num_solve += 1;
        let mut assumption;
        if self.propagate() != CREF_NONE {
            self.trivial_unsat = true;
            self.unsat_core.clear();
            return false;
        }
        let assump = if !constraint.is_empty() {
            assumption = LitVec::new();
            assumption.push(self.constrain_act.lit());
            assumption.extend_from_slice(assump);
            let mut cc = Vec::new();
            for c in constraint.iter() {
                for l in c.iter() {
                    cc.push(*l);
                }
            }
            if !self.new_round(
                assump.iter().chain(cc.iter()).map(|l| l.var()),
                constraint,
                bucket,
            ) {
                self.unsat_core.clear();
                return false;
            };
            &assumption
        } else {
            assert!(self.new_round(assump.iter().map(|l| l.var()), vec![], bucket));
            assump
        };
        self.clean_leanrt(true);
        self.simplify();
        self.search_with_restart(assump)
    }

    pub fn solve(&mut self, assump: &[Lit], constraint: Vec<LitVec>) -> bool {
        self.solve_inner(assump, constraint, true)
    }

    pub fn solve_without_bucket(&mut self, assump: &[Lit], constraint: Vec<LitVec>) -> bool {
        self.solve_inner(assump, constraint, false)
    }

    pub fn inductive_with_constrain(
        &mut self,
        cube: &[Lit],
        strengthen: bool,
        mut constraint: Vec<LitVec>,
    ) -> bool {
        let assump = self.ts.lits_next(cube);
        if strengthen {
            constraint.push(LitVec::from_iter(cube.iter().map(|l| !*l)));
        }
        !self.solve(&assump, constraint.clone())
    }

    pub fn inductive(&mut self, cube: &[Lit], strengthen: bool) -> bool {
        self.inductive_with_constrain(cube, strengthen, vec![])
    }

    pub fn inductive_core(&mut self) -> LitVec {
        let mut ans = LitVec::new();
        for l in self.assump.iter() {
            if self.unsat_has(*l) {
                ans.push(self.ts.prev(*l));
            }
        }
        if self.ts.cube_subsume_init(&ans) {
            ans = LitVec::new();
            let new = self
                .assump
                .iter()
                .find(|l| {
                    let l = self.ts.prev(**l);
                    self.ts.init_map[l.var()].is_some_and(|i| i != l.polarity())
                })
                .unwrap();
            for l in self.assump.iter() {
                if self.unsat_has(*l) || l.eq(new) {
                    ans.push(self.ts.prev(*l));
                }
            }
            assert!(!self.ts.cube_subsume_init(&ans));
        }
        ans
    }

    #[allow(unused)]
    pub fn imply<'a>(
        &mut self,
        domain: impl Iterator<Item = Var>,
        assump: impl Iterator<Item = &'a Lit>,
    ) {
        self.reset();
        self.domain.enable_local(domain, &self.ts, &self.value);
        self.new_level();
        for a in assump {
            if let Lbool::FALSE = self.value.v(*a) {
                panic!();
            }
            self.assign(*a, CREF_NONE);
        }
        assert!(self.propagate() == CREF_NONE);
    }

    pub fn set_domain(&mut self, domain: impl Iterator<Item = Lit>) {
        self.reset();
        self.temporary_domain = true;
        self.domain
            .enable_local(domain.map(|l| l.var()), &self.ts, &self.value);
        assert!(!self.domain.has(self.constrain_act));
        self.domain.insert(self.constrain_act);
        self.vsids.enable_bucket = true;
        self.vsids.bucket.clear();
        self.push_to_vsids();
    }

    pub fn unset_domain(&mut self) {
        self.temporary_domain = false;
    }

    #[inline]
    pub fn get_last_assump(&self) -> &LitVec {
        &self.assump
    }

    #[inline]
    #[allow(unused)]
    pub fn assert_value(&mut self, lit: Lit) -> Option<bool> {
        self.reset();
        self.value.v(lit).into()
    }

    #[allow(unused)]
    pub fn trivial_predecessor(&mut self) -> LitVec {
        let mut latchs = LitVec::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            if let Some(v) = self.sat_value(lit) {
                // if !self.flip_to_none(*latch) {
                latchs.push(lit.not_if(!v));
                // }
            }
        }
        latchs
    }
}

impl Satif for Solver {
    #[inline]
    fn new_var(&mut self) -> Var {
        self.reset();
        let v = self.constrain_act;
        let var = Var::new(self.num_var() + 1);
        self.value.reserve(var);
        self.level.reserve(var);
        self.reason.reserve(var);
        self.watchers.reserve(var);
        self.vsids.reserve(var);
        self.phase_saving.reserve(var);
        self.analyze.reserve(var);
        self.unsat_core.reserve(var);
        self.domain.reserve(var);
        self.mark.reserve(var);
        self.constrain_act = var;
        v
    }

    #[inline]
    fn num_var(&self) -> usize {
        self.constrain_act.into()
    }

    fn add_clause(&mut self, _clause: &[Lit]) {
        todo!()
    }

    fn solve(&mut self, assumps: &[Lit]) -> bool {
        self.solve_inner(assumps, vec![], true)
    }

    fn solve_with_constraint(&mut self, assumps: &[Lit], constraint: Vec<LitVec>) -> bool {
        self.solve_inner(assumps, constraint, true)
    }

    #[inline]
    fn sat_value(&self, lit: Lit) -> Option<bool> {
        match self.value.v(lit) {
            Lbool::TRUE => Some(true),
            Lbool::FALSE => Some(false),
            _ => None,
        }
    }

    #[inline]
    fn unsat_has(&self, lit: Lit) -> bool {
        self.unsat_core.has(lit)
    }
}
