mod analyze;
mod cdb;
mod domain;
mod propagate;
mod search;
mod simplify;
pub mod statistic;
mod utils;
mod vsids;

use crate::{frame::Frames, options::Options, transys::Transys, IC3};
use analyze::Analyze;
use cdb::{CRef, ClauseDB, ClauseKind, CREF_NONE};
use domain::Domain;
use giputils::gvec::Gvec;
use logic_form::{Clause, Cube, Lemma, Lit, LitSet, Var, VarMap};
use propagate::Watchers;
use rand::{prelude::SliceRandom, rngs::StdRng, SeedableRng};
use search::Value;
use simplify::Simplify;
use statistic::SolverStatistic;
use std::{
    collections::HashSet,
    ops::{Deref, DerefMut, Index, IndexMut},
    rc::Rc,
    slice,
    time::Instant,
};
use utils::Lbool;
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
    domain: Domain,
    temporary_domain: bool,
    prepared_vsids: bool,
    constrain_act: Var,

    ts: Rc<Transys>,
    _frame: Frames,

    assump: Cube,
    constrain: Vec<Clause>,

    trivial_unsat: bool,
    mark: LitSet,
    rng: StdRng,
    pub statistic: SolverStatistic,
    #[allow(unused)]
    options: Options,
}

impl Solver {
    pub fn new(options: Options, id: Option<usize>, ts: &Rc<Transys>, frame: &Frames) -> Self {
        let mut solver = Self {
            id,
            ts: ts.clone(),
            _frame: frame.clone(),
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
            constrain: Default::default(),
            statistic: Default::default(),
            trivial_unsat: false,
            rng: StdRng::seed_from_u64(options.rseed),
            mark: Default::default(),
            options,
        };
        while solver.num_var() < solver.ts.num_var() {
            solver.new_var();
        }
        for cls in ts.trans.iter() {
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

    pub fn new_var(&mut self) -> Var {
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
    pub fn num_var(&self) -> usize {
        self.constrain_act.into()
    }

    fn simplify_clause(&mut self, cls: &[Lit]) -> Option<logic_form::Clause> {
        assert!(self.highest_level() == 0);
        let mut clause = logic_form::Clause::new();
        for l in cls.iter() {
            assert!(self.num_var() + 1 > l.var().into());
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
    // self.simplify.lazy_remove.push(Cube::from(lemma));
    // }

    #[allow(unused)]
    pub fn lemmas(&mut self) -> Vec<Lemma> {
        self.reset();
        let mut lemmas = Vec::new();
        for t in self.trail.iter() {
            if self.ts.is_latch(t.var()) {
                lemmas.push(Lemma::new(Cube::from([!*t])));
            }
        }
        for l in self.cdb.lemmas.iter() {
            let lemma = Cube::from_iter(self.cdb.get(*l).slice().iter().map(|l| !*l));
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
        constrain: Vec<Clause>,
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

        for mut c in constrain {
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

    pub fn solve_with_domain(
        &mut self,
        assump: &[Lit],
        constrain: Vec<Clause>,
        bucket: bool,
        limit: bool,
    ) -> Option<bool> {
        if self.trivial_unsat {
            self.unsat_core.clear();
            return Some(false);
        }
        assert!(!assump.is_empty());
        self.statistic.num_solve += 1;
        let mut assumption;
        if self.propagate() != CREF_NONE {
            self.trivial_unsat = true;
            self.unsat_core.clear();
            return Some(false);
        }
        let assump = if !constrain.is_empty() {
            assumption = Cube::new();
            assumption.push(self.constrain_act.lit());
            assumption.extend_from_slice(assump);
            let mut cc = Vec::new();
            for c in constrain.iter() {
                for l in c.iter() {
                    cc.push(*l);
                }
            }
            if !self.new_round(
                assump.iter().chain(cc.iter()).map(|l| l.var()),
                constrain,
                bucket,
            ) {
                self.unsat_core.clear();
                return Some(false);
            };
            &assumption
        } else {
            assert!(self.new_round(assump.iter().map(|l| l.var()), vec![], bucket));
            assump
        };
        self.clean_leanrt(true);
        self.simplify();
        self.search_with_restart(assump, limit)
    }

    pub fn inductive_with_constrain(
        &mut self,
        cube: &[Lit],
        strengthen: bool,
        mut constrain: Vec<Clause>,
        limit: bool,
    ) -> Option<bool> {
        let assump = self.ts.cube_next(cube);
        if strengthen {
            constrain.push(Clause::from_iter(cube.iter().map(|l| !*l)));
        }
        let res = self
            .solve_with_domain(&assump, constrain.clone(), true, limit)
            .map(|l| !l);
        self.assump = assump;
        self.constrain = constrain;
        res
    }

    pub fn inductive(&mut self, cube: &[Lit], strengthen: bool, limit: bool) -> Option<bool> {
        self.inductive_with_constrain(cube, strengthen, vec![], limit)
    }

    pub fn inductive_core(&mut self) -> Cube {
        let mut ans = Cube::new();
        for l in self.assump.iter() {
            if self.unsat_has(*l) {
                ans.push(self.ts.lit_prev(*l));
            }
        }
        if self.ts.cube_subsume_init(&ans) {
            ans = Cube::new();
            let new = self
                .assump
                .iter()
                .find(|l| {
                    let l = self.ts.lit_prev(**l);
                    self.ts.init_map[l.var()].is_some_and(|i| i != l.polarity())
                })
                .unwrap();
            for l in self.assump.iter() {
                if self.unsat_has(*l) || l.eq(new) {
                    ans.push(self.ts.lit_prev(*l));
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
    pub fn sat_value(&self, lit: Lit) -> Option<bool> {
        match self.value.v(lit) {
            Lbool::TRUE => Some(true),
            Lbool::FALSE => Some(false),
            _ => None,
        }
    }

    #[inline]
    pub fn unsat_has(&self, lit: Lit) -> bool {
        self.unsat_core.has(lit)
    }

    #[inline]
    #[allow(unused)]
    pub fn assert_value(&mut self, lit: Lit) -> Option<bool> {
        self.reset();
        self.value.v(lit).into()
    }

    #[allow(unused)]
    pub fn trivial_predecessor(&mut self) -> Cube {
        let mut latchs = Cube::new();
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

pub struct Solvers {
    solvers: Vec<Solver>,
}

impl Deref for Solvers {
    type Target = Solver;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.solvers[0]
    }
}

impl DerefMut for Solvers {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.solvers[0]
    }
}

impl Index<usize> for Solvers {
    type Output = Solver;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.solvers[index]
    }
}

impl IndexMut<usize> for Solvers {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.solvers[index]
    }
}

impl Solvers {
    #[inline]
    pub fn new<F>(f: F, num: usize) -> Self
    where
        F: Fn() -> Solver,
    {
        let mut solvers = Vec::new();
        for _ in 0..num {
            solvers.push(f());
        }
        Self { solvers }
    }

    #[inline]
    pub fn new_var_for_all(&mut self) -> Var {
        let v = self.solvers[0].new_var();
        for s in self.solvers[1..].iter_mut() {
            assert!(s.new_var() == v);
        }
        v
    }

    #[inline]
    pub fn add_lemma_for_all(&mut self, lemma: &[Lit]) {
        for s in self.solvers.iter_mut() {
            s.add_lemma(lemma);
        }
    }

    #[inline]
    pub fn iter(&self) -> slice::Iter<'_, Solver> {
        self.solvers.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, Solver> {
        self.solvers.iter_mut()
    }
}

impl IC3 {
    pub fn get_bad(&mut self) -> Option<(Cube, Cube)> {
        self.statistic.num_get_bad += 1;
        let start = Instant::now();
        let solver = self.solvers.last_mut().unwrap();
        solver.assump = self.ts.bad.clone();
        solver.constrain = Default::default();
        let res = solver
            .solve_with_domain(&self.ts.bad, vec![], false, false)
            .unwrap();
        self.statistic.block_get_bad_time += start.elapsed();
        if res {
            let frame = self.solvers.len();
            Some(self.get_predecessor(frame, true))
        } else {
            None
        }
    }
}

impl IC3 {
    #[inline]
    pub fn sat_contained(&mut self, frame: usize, lemma: &Lemma) -> bool {
        !self.solvers[frame]
            .solve_with_domain(lemma, vec![], true, false)
            .unwrap()
    }

    pub fn blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &Cube,
        ascending: bool,
        strengthen: bool,
        limit: bool,
    ) -> Option<bool> {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.solvers[frame - 1].inductive(&ordered_cube, strengthen, limit)
    }

    pub fn blocked_with_ordered_with_constrain(
        &mut self,
        frame: usize,
        cube: &Cube,
        ascending: bool,
        strengthen: bool,
        constrain: Vec<Clause>,
        limit: bool,
    ) -> Option<bool> {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.solvers[frame - 1].inductive_with_constrain(
            &ordered_cube,
            strengthen,
            constrain,
            limit,
        )
    }

    #[inline]
    fn minimal_predecessor(
        lift: &mut Solver,
        inputs: &[Lit],
        latchs: &[Lit],
        target_constrain: &Clause,
    ) -> Option<Cube> {
        let assump = Cube::from_iter(inputs.iter().chain(latchs.iter()).copied());
        if lift
            .solve_with_domain(&assump, vec![target_constrain.clone()], true, false)
            .unwrap()
        {
            return None;
        }
        Some(
            latchs
                .iter()
                .filter(|l| lift.unsat_has(**l))
                .copied()
                .collect(),
        )
    }

    pub fn get_predecessor(&mut self, frame: usize, strengthen: bool) -> (Cube, Cube) {
        let start = Instant::now();
        let solver = &mut self.solvers[frame - 1];
        let mut cls: Cube = solver.assump.clone();
        cls.extend_from_slice(&self.abs_cst);
        if cls.is_empty() {
            return (Cube::new(), Cube::new());
        }
        let in_cls: HashSet<Var> = HashSet::from_iter(cls.iter().map(|l| l.var()));
        let cls = !cls;
        let mut inputs = Cube::new();
        for input in self.ts.inputs.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        self.lift.set_domain(cls.iter().cloned());
        let mut latchs = Cube::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            if self.lift.domain.has(lit.var()) {
                if let Some(v) = solver.sat_value(lit) {
                    if in_cls.contains(latch) || !solver.flip_to_none(*latch) {
                        latchs.push(lit.not_if(!v));
                    }
                }
            }
        }
        let inn: Box<dyn FnMut(&mut Cube)> = Box::new(|cube: &mut Cube| {
            cube.sort();
            cube.reverse();
        });
        let act: Box<dyn FnMut(&mut Cube)> = Box::new(|cube: &mut Cube| {
            self.activity.sort_by_activity(cube, false);
        });
        let rev: Box<dyn FnMut(&mut Cube)> = Box::new(|cube: &mut Cube| {
            cube.reverse();
        });
        let mut order = if self.options.ic3.inn {
            vec![inn, act, rev]
        } else {
            vec![act, rev]
        };
        for i in 0.. {
            if latchs.is_empty() {
                break;
            }
            if let Some(f) = order.get_mut(i) {
                f(&mut latchs);
            } else {
                latchs.shuffle(&mut self.lift.rng);
            }
            let olen = latchs.len();
            latchs = Self::minimal_predecessor(&mut self.lift, &inputs, &latchs, &cls).unwrap();
            if latchs.len() == olen || !strengthen {
                break;
            }
        }
        self.lift.unset_domain();
        self.statistic.block_get_predecessor_time += start.elapsed();
        (latchs, inputs)
    }

    pub fn new_var(&mut self) -> Var {
        let ts = unsafe { Rc::get_mut_unchecked(&mut self.ts) };
        let var = ts.new_var();
        for s in self.solvers.iter_mut() {
            assert!(var == s.new_var_for_all());
        }
        assert!(var == self.lift.new_var());
        var
    }

    pub fn add_latch(
        &mut self,
        state: Var,
        next: Lit,
        init: Option<bool>,
        mut trans: Vec<Clause>,
        dep: Vec<Var>,
    ) {
        for i in 0..trans.len() {
            let mut nt = Clause::new();
            for l in trans[i].iter() {
                nt.push(if l.var() == state {
                    next.not_if(!l.polarity())
                } else {
                    self.ts.lit_next(*l)
                });
            }
            trans.push(nt);
        }
        let ts = unsafe { Rc::get_mut_unchecked(&mut self.ts) };
        ts.add_latch(state, next, init, trans.clone(), dep.clone());
        let tmp_lit_set = unsafe { Rc::get_mut_unchecked(&mut self.frame.tmp_lit_set) };
        tmp_lit_set.reserve(ts.max_latch);
        let handle_s = |s: &mut Solver| {
            s.reset();
            for cls in trans.iter() {
                s.add_clause_inner(cls, ClauseKind::Trans);
            }
            s.add_domain(state, true);
        };
        for s in self.solvers.iter_mut() {
            for s in s.iter_mut() {
                handle_s(s);
            }
        }
        handle_s(&mut self.lift);
        if !self.solvers[0].value.v(state.lit()).is_none() {
            if self.solvers[0].value.v(state.lit()).is_true() {
                ts.init.push(state.lit());
                ts.init_map[state] = Some(true);
            } else {
                ts.init.push(!state.lit());
                ts.init_map[state] = Some(false);
            }
        } else if !self.solvers[0]
            .solve_with_domain(&[state.lit()], vec![], true, false)
            .unwrap()
        {
            ts.init.push(!state.lit());
            ts.init_map[state] = Some(false);
        } else if !self.solvers[0]
            .solve_with_domain(&[!state.lit()], vec![], true, false)
            .unwrap()
        {
            ts.init.push(state.lit());
            ts.init_map[state] = Some(true);
        }

        self.activity.reserve(state);
        // self.activity.set_max_act(state);
        self.auxiliary_var.push(state);
    }
}
