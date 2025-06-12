mod analyze;
mod cdb;
mod domain;
mod propagate;
mod search;
mod simplify;
mod statistic;
mod ts;
mod vsids;

use analyze::Analyze;
pub use cdb::ClauseKind;
use cdb::{CREF_NONE, CRef, ClauseDB};
use domain::Domain;
use giputils::gvec::Gvec;
use logic_form::{DagCnf, Lbool, VarAssign};
use logic_form::{Lit, LitSet, LitVec, Var, VarMap};
use propagate::Watchers;
use rand::{SeedableRng, rngs::StdRng};
use satif::Satif;
use simplify::Simplify;
pub use statistic::SolverStatistic;
use std::time::Duration;
pub use ts::*;
use vsids::Vsids;

pub struct DagCnfSolver {
    cdb: ClauseDB,
    watchers: Watchers,
    value: VarAssign,
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
    domain: Domain,
    temporary_domain: bool,
    prepared_vsids: bool,
    constrain_act: Var,
    dc: DagCnf,
    trivial_unsat: bool,
    mark: LitSet,
    rng: StdRng,

    assump: LitVec,
    constraint: Vec<LitVec>,

    statistic: SolverStatistic,
}

impl DagCnfSolver {
    pub fn new(dc: &DagCnf, rseed: u64) -> Self {
        let constrain_act = Var::CONST;
        let mut solver = Self {
            dc: dc.clone(),
            cdb: Default::default(),
            watchers: Default::default(),
            value: VarAssign::new_with(constrain_act),
            trail: Default::default(),
            pos_in_trail: Default::default(),
            level: VarMap::new_with(constrain_act),
            reason: VarMap::new_with(constrain_act),
            propagated: Default::default(),
            vsids: Default::default(),
            phase_saving: Default::default(),
            analyze: Default::default(),
            simplify: Default::default(),
            unsat_core: Default::default(),
            domain: Domain::new(),
            temporary_domain: Default::default(),
            prepared_vsids: false,
            constrain_act,
            assump: Default::default(),
            constraint: Default::default(),
            statistic: Default::default(),
            trivial_unsat: false,
            rng: StdRng::seed_from_u64(rseed),
            mark: Default::default(),
        };
        while solver.num_var() < solver.dc.num_var() {
            solver.new_var();
        }
        for cls in dc.clause() {
            solver.add_clause_inner(cls, ClauseKind::Trans);
        }
        assert!(solver.propagate() == CREF_NONE);
        solver
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

    fn add_clause_inner(&mut self, clause: &[Lit], mut kind: ClauseKind) -> CRef {
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

    // #[allow(unused)]
    // pub fn lemmas(&mut self) -> Vec<LitOrdVec> {
    //     self.reset();
    //     let mut lemmas = Vec::new();
    //     for t in self.trail.iter() {
    //         if self.dc.is_latch(t.var()) {
    //             lemmas.push(LitOrdVec::new(LitVec::from([!*t])));
    //         }
    //     }
    //     for l in self.cdb.lemmas.iter() {
    //         let lemma = LitVec::from_iter(self.cdb.get(*l).slice().iter().map(|l| !*l));
    //         lemmas.push(LitOrdVec::new(lemma));
    //     }
    //     lemmas
    // }

    fn reset(&mut self) {
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
            self.domain.enable_local(domain, &self.dc, &self.value);
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
            self.domain.len() as f64 / (self.dc.num_var() - self.trail.len()) as f64;
        true
    }

    fn solve_inner(
        &mut self,
        assump: &[Lit],
        constraint: Vec<LitVec>,
        limit: Option<Duration>,
    ) -> Option<bool> {
        self.assump = assump.into();
        self.constraint = constraint.clone();
        if self.trivial_unsat {
            self.unsat_core.clear();
            return Some(false);
        }
        self.statistic.num_solve += 1;
        let mut assumption;
        if self.propagate() != CREF_NONE {
            self.trivial_unsat = true;
            self.unsat_core.clear();
            return Some(false);
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
                true,
            ) {
                self.unsat_core.clear();
                return Some(false);
            };
            &assumption
        } else {
            assert!(self.new_round(assump.iter().map(|l| l.var()), vec![], true));
            assump
        };
        self.clean_leanrt(true);
        self.simplify();
        self.search_with_restart(assump, limit)
    }

    #[allow(unused)]
    pub fn imply<'a>(
        &mut self,
        domain: impl Iterator<Item = Var>,
        assump: impl Iterator<Item = &'a Lit>,
    ) {
        self.reset();
        self.domain.enable_local(domain, &self.dc, &self.value);
        self.new_level();
        for a in assump {
            if let Lbool::FALSE = self.value.v(*a) {
                panic!();
            }
            self.assign(*a, CREF_NONE);
        }
        assert!(self.propagate() == CREF_NONE);
    }

    #[inline]
    pub fn domain_has(&self, var: Var) -> bool {
        self.domain.has(var)
    }

    pub fn set_domain(&mut self, domain: impl IntoIterator<Item = Lit>) {
        self.reset();
        self.temporary_domain = true;
        self.domain
            .enable_local(domain.into_iter().map(|l| l.var()), &self.dc, &self.value);
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
    #[allow(unused)]
    pub fn assert_value(&mut self, lit: Lit) -> Option<bool> {
        self.reset();
        self.value.v(lit).into()
    }

    #[inline]
    pub fn statistic(&self) -> &SolverStatistic {
        &self.statistic
    }
}

impl Satif for DagCnfSolver {
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

    fn add_clause(&mut self, clause: &[Lit]) {
        self.reset();
        for l in clause.iter() {
            self.add_domain(l.var(), true);
        }
        self.add_clause_inner(clause, ClauseKind::Lemma);
    }

    fn solve(&mut self, assumps: &[Lit]) -> bool {
        self.solve_inner(assumps, vec![], None).unwrap()
    }

    fn solve_with_constraint(&mut self, assumps: &[Lit], constraint: Vec<LitVec>) -> bool {
        self.solve_inner(assumps, constraint, None).unwrap()
    }

    fn solve_with_limit(
        &mut self,
        assumps: &[Lit],
        constraint: Vec<LitVec>,
        limit: Duration,
    ) -> Option<bool> {
        self.solve_inner(assumps, constraint, Some(limit))
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
