use crate::{
    Engine, Proof, Witness,
    config::Config,
    gipsat::{SolverStatistic, TransysSolver},
    ic3::frame::FrameLemma,
    transys::{Transys, TransysCtx, TransysIf, frts::FrTs, unroll::TransysUnroll},
};
use activity::Activity;
use frame::{Frame, Frames};
use giputils::{grc::Grc, hash::GHashMap, logger::IntervalLogger};
use log::{Level, debug, info};
use logicrs::{Lit, LitOrdVec, LitVec, Var, VarVMap, satif::Satif};
use mic::{DropVarParameter, MicType};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{Rng, SeedableRng, rngs::StdRng, seq::SliceRandom};
use statistic::Statistic;
use std::time::Instant;

mod activity;
mod aux;
mod frame;
mod mic;
mod proofoblig;
mod solver;
mod statistic;
mod verify;

pub struct IC3 {
    cfg: Config,
    ts: Transys,
    tsctx: Grc<TransysCtx>,
    solvers: Vec<TransysSolver>,
    inf_solver: TransysSolver,
    lift: TransysSolver,
    bad_ts: Grc<TransysCtx>,
    bad_solver: cadical::Solver,
    bad_lift: TransysSolver,
    bad_input: GHashMap<Var, Var>,
    frame: Frames,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    pre_lemmas: Vec<LitVec>,
    abs_cst: LitVec,
    bmc_solver: Option<(Box<dyn Satif>, TransysUnroll<Transys>)>,
    ots: Transys,
    rst: VarVMap,
    auxiliary_var: Vec<Var>,
    rng: StdRng,

    filog: IntervalLogger,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        if !self.cfg.ic3.no_pred_prop {
            self.bad_solver = cadical::Solver::new();
            self.bad_ts.load_trans(&mut self.bad_solver, true);
            for lemma in self.frame.inf.iter() {
                self.bad_solver.add_clause(&!lemma.cube());
            }
        }
        let mut solver = TransysSolver::new(&self.tsctx, true, self.rng.random());
        for lemma in self.frame.inf.iter() {
            solver.add_clause(&!lemma.cube());
        }
        for v in self.auxiliary_var.iter() {
            solver.add_domain(*v, true);
        }
        self.solvers.push(solver);
        self.frame.push(Frame::new());
        if self.level() == 0 {
            for init in self.tsctx.init.clone() {
                self.add_lemma(0, !init, true, None);
            }
            let mut init = LitVec::new();
            for l in self.tsctx.latch.iter() {
                if self.tsctx.init_map[*l].is_none()
                    && let Some(v) = self.solvers[0].sat_value(l.lit())
                {
                    let l = l.lit().not_if(!v);
                    init.push(l);
                }
            }
            for i in init {
                self.ts.add_init(i.var(), Lit::constant(i.polarity()));
                self.tsctx.add_init(i.var(), Lit::constant(i.polarity()));
            }
        } else if self.level() == 1 {
            for cls in self.pre_lemmas.clone().iter() {
                self.add_lemma(1, !cls.clone(), true, None);
            }
        }
    }

    fn push_lemma(&mut self, frame: usize, mut cube: LitVec) -> (usize, LitVec) {
        let start = Instant::now();
        for i in frame + 1..=self.level() {
            if self.solvers[i - 1].inductive(&cube, true) {
                cube = self.solvers[i - 1].inductive_core();
            } else {
                return (i, cube);
            }
        }
        self.statistic.block.push_time += start.elapsed();
        (self.level() + 1, cube)
    }

    fn generalize(&mut self, mut po: ProofObligation, mic_type: MicType) -> bool {
        if self.cfg.ic3.inn && self.tsctx.cube_subsume_init(&po.lemma) {
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.lemma.cube().clone(), false, Some(po));
        }
        let mut mic = self.solvers[po.frame - 1].inductive_core();
        mic = self.mic(po.frame, mic, &[], mic_type);
        let (frame, mic) = self.push_lemma(po.frame, mic);
        self.statistic.avg_po_cube_len += po.lemma.len();
        po.push_to(frame);
        self.add_obligation(po.clone());
        if self.add_lemma(frame - 1, mic.clone(), false, Some(po)) {
            return true;
        }
        false
    }

    fn block(&mut self) -> Option<bool> {
        while let Some(mut po) = self.obligations.pop(self.level()) {
            if po.removed {
                continue;
            }
            if self.tsctx.cube_subsume_init(&po.lemma) {
                if self.cfg.ic3.abs_cst {
                    self.add_obligation(po.clone());
                    if let Some(c) = self.check_witness_by_bmc(po.clone()) {
                        for c in c {
                            assert!(!self.abs_cst.contains(&c));
                            self.abs_cst.push(c);
                        }
                        info!("abs cst len: {}", self.abs_cst.len(),);
                        self.obligations.clear();
                        for f in self.frame.iter_mut() {
                            for l in f.iter_mut() {
                                l.po = None;
                            }
                        }
                        continue;
                    } else {
                        return Some(false);
                    }
                } else if po.frame > 0 {
                    debug_assert!(!self.solvers[0].solve(&po.lemma));
                } else {
                    self.add_obligation(po.clone());
                    return Some(false);
                }
            }
            if let Some((bf, _)) = self.frame.trivial_contained(Some(po.frame), &po.lemma) {
                if let Some(bf) = bf {
                    po.push_to(bf + 1);
                    self.add_obligation(po);
                }
                continue;
            }
            debug!("{}", self.frame.statistic(false));
            po.bump_act();
            let blocked_start = Instant::now();
            let blocked = self.blocked_with_ordered(po.frame, &po.lemma, false, false);
            self.statistic.block.blocked_time += blocked_start.elapsed();
            if blocked {
                let mic_type = if self.cfg.ic3.dynamic {
                    if let Some(mut n) = po.next.as_mut() {
                        let mut act = n.act;
                        for _ in 0..2 {
                            if let Some(nn) = n.next.as_mut() {
                                n = nn;
                                act = act.max(n.act);
                            } else {
                                break;
                            }
                        }
                        const CTG_THRESHOLD: f64 = 10.0;
                        const EXCTG_THRESHOLD: f64 = 40.0;
                        let (limit, max, level) = match act {
                            EXCTG_THRESHOLD.. => {
                                let limit = ((act - EXCTG_THRESHOLD).powf(0.3) * 2.0 + 5.0).round()
                                    as usize;
                                (limit, 5, 1)
                            }
                            CTG_THRESHOLD..EXCTG_THRESHOLD => {
                                let max = (act - CTG_THRESHOLD) as usize / 10 + 2;
                                (1, max, 1)
                            }
                            ..CTG_THRESHOLD => (0, 0, 0),
                            _ => panic!(),
                        };
                        let p = DropVarParameter::new(limit, max, level);
                        MicType::DropVar(p)
                    } else {
                        MicType::DropVar(Default::default())
                    }
                } else {
                    MicType::from_config(&self.cfg)
                };
                if self.generalize(po, mic_type) {
                    return None;
                }
            } else {
                let (model, inputs) = self.get_pred(po.frame, true);
                self.add_obligation(ProofObligation::new(
                    po.frame - 1,
                    LitOrdVec::new(model),
                    vec![inputs],
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.add_obligation(po);
            }
        }
        Some(true)
    }

    #[allow(unused)]
    fn trivial_block_rec(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
        constraint: &[LitVec],
        limit: &mut usize,
        parameter: DropVarParameter,
    ) -> bool {
        if frame == 0 {
            return false;
        }
        if self.tsctx.cube_subsume_init(&lemma) {
            return false;
        }
        if *limit == 0 {
            return false;
        }
        *limit -= 1;
        loop {
            if self.blocked_with_ordered_with_constrain(
                frame,
                &lemma,
                false,
                true,
                constraint.to_vec(),
            ) {
                let mut mic = self.solvers[frame - 1].inductive_core();
                mic = self.mic(frame, mic, constraint, MicType::DropVar(parameter));
                let (frame, mic) = self.push_lemma(frame, mic);
                self.add_lemma(frame - 1, mic, false, None);
                return true;
            } else {
                if *limit == 0 {
                    return false;
                }
                let model = LitOrdVec::new(self.get_pred(frame, false).0);
                if !self.trivial_block_rec(frame - 1, model, constraint, limit, parameter) {
                    return false;
                }
            }
        }
    }

    fn trivial_block(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> bool {
        let mut limit = parameter.limit;
        self.trivial_block_rec(frame, lemma, constraint, &mut limit, parameter)
    }

    fn propagate(&mut self, from: Option<usize>) -> bool {
        let level = self.level();
        let from = from.unwrap_or(self.frame.early).max(1);
        for frame_idx in from..level {
            self.frame[frame_idx].sort_by_key(|x| x.len());
            let frame = self.frame[frame_idx].clone();
            for mut lemma in frame {
                if self.frame[frame_idx].iter().all(|l| l.ne(&lemma)) {
                    continue;
                }
                for ctp in 0..3 {
                    if self.blocked_with_ordered(frame_idx + 1, &lemma, false, false) {
                        let core = if self.cfg.ic3.inn && self.tsctx.cube_subsume_init(&lemma) {
                            lemma.cube().clone()
                        } else {
                            self.solvers[frame_idx].inductive_core()
                        };
                        if let Some(po) = &mut lemma.po
                            && po.frame < frame_idx + 2
                            && self.obligations.remove(po)
                        {
                            po.push_to(frame_idx + 2);
                            self.obligations.add(po.clone());
                        }
                        self.add_lemma(frame_idx + 1, core, true, lemma.po);
                        self.statistic.ctp.statistic(ctp > 0);
                        break;
                    }
                    if !self.cfg.ic3.ctp {
                        break;
                    }
                    let (ctp, _) = self.get_pred(frame_idx + 1, false);
                    if !self.tsctx.cube_subsume_init(&ctp)
                        && self.solvers[frame_idx - 1].inductive(&ctp, true)
                    {
                        let core = self.solvers[frame_idx - 1].inductive_core();
                        let mic =
                            self.mic(frame_idx, core, &[], MicType::DropVar(Default::default()));
                        if self.add_lemma(frame_idx, mic, false, None) {
                            return true;
                        }
                    } else {
                        break;
                    }
                }
            }
            if self.frame[frame_idx].is_empty() {
                return true;
            }
        }
        self.frame.early = self.level();
        false
    }

    fn propagete_to_inf_rec(&mut self, lastf: &mut Vec<FrameLemma>, ctp: LitVec) -> bool {
        let ctp = LitOrdVec::new(ctp);
        let Some(lidx) = lastf.iter().position(|l| l.subsume(&ctp)) else {
            return false;
        };
        let mut lemma = lastf.swap_remove(lidx);
        loop {
            if self.inf_solver.inductive(&lemma, true) {
                if let Some(po) = &mut lemma.po {
                    self.obligations.remove(po);
                }
                self.add_inf_lemma(lemma.cube().clone());
                return true;
            } else {
                let target = self.tsctx.lits_next(lemma.cube());
                let (ctp, _) = self.lift.get_pred(&self.inf_solver, &target, false);
                if !self.propagete_to_inf_rec(lastf, ctp) {
                    return false;
                }
            }
        }
    }

    fn propagete_to_inf(&mut self) {
        let level = self.level();
        self.frame[level].shuffle(&mut self.rng);
        let mut lastf = self.frame[level].clone();
        while let Some(mut lemma) = lastf.pop() {
            loop {
                if self.inf_solver.inductive(&lemma, true) {
                    if let Some(po) = &mut lemma.po {
                        self.obligations.remove(po);
                    }
                    self.add_inf_lemma(lemma.cube().clone());
                    break;
                } else {
                    let target = self.tsctx.lits_next(lemma.cube());
                    let (ctp, _) = self.lift.get_pred(&self.inf_solver, &target, false);
                    if !self.propagete_to_inf_rec(&mut lastf, ctp) {
                        break;
                    }
                }
            }
        }
    }

    fn base(&mut self) -> bool {
        self.extend();
        assert!(self.level() == 0);
        if !self.cfg.ic3.no_pred_prop {
            let bad = self.tsctx.bad;
            if self.solvers[0].solve(&self.tsctx.bad.cube()) {
                let (input, bad) = self.solvers[0].trivial_pred();
                self.add_obligation(ProofObligation::new(
                    0,
                    LitOrdVec::new(bad),
                    vec![input],
                    0,
                    None,
                ));
                info!("counter-example found in base checking");
                return false;
            }
            self.tsctx.constraint.push(!bad);
            self.ts.constraint.push(!bad);
            self.lift = TransysSolver::new(&self.tsctx, false, self.rng.random());
            self.inf_solver = TransysSolver::new(&self.tsctx, true, self.rng.random());
        }
        true
    }
}

impl IC3 {
    pub fn new(mut cfg: Config, mut ts: Transys, pre_lemmas: Vec<LitVec>) -> Self {
        let ots = ts.clone();
        let mut rng = StdRng::seed_from_u64(cfg.rseed);
        let mut rst = VarVMap::new_self_map(ts.max_var());
        ts = ts.check_liveness_and_l2s(&mut rst);
        let statistic = Statistic::default();
        if !cfg.preproc.no_preproc {
            ts.simplify(&mut rst);
            let frts = FrTs::new(ts, rng.random(), rst, vec![]);
            (ts, rst) = frts.fr();
        }
        info!("simplified ts has {}", ts.statistic());
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if cfg.ic3.inn {
            cfg.ic3.no_pred_prop = true;
            ts = uts.interal_signals();
        }
        let mut bad_input = GHashMap::new();
        for &l in ts.input.iter() {
            bad_input.insert(uts.var_next(l, 1), l);
        }
        let mut bad_ts = uts.compile();
        bad_ts.constraint.extend(ts.bad.iter().map(|&l| !l));
        let tsctx = Grc::new(ts.ctx());
        let bad_ts = Grc::new(bad_ts.ctx());
        let activity = Activity::new(&tsctx);
        let frame = Frames::new(&tsctx);
        let inf_solver = TransysSolver::new(&tsctx, true, rng.random());
        let lift = TransysSolver::new(&tsctx, false, rng.random());
        let bad_lift = TransysSolver::new(&bad_ts, false, rng.random());
        let abs_cst = if cfg.ic3.abs_cst {
            LitVec::new()
        } else {
            ts.constraint.clone()
        };
        Self {
            cfg,
            ts,
            tsctx,
            activity,
            solvers: Vec::new(),
            inf_solver,
            bad_ts,
            bad_solver: cadical::Solver::new(),
            bad_lift,
            bad_input,
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
            abs_cst,
            pre_lemmas,
            auxiliary_var: Vec::new(),
            ots,
            rst,
            bmc_solver: None,
            rng,
            filog: Default::default(),
        }
    }

    pub fn invariant(&self) -> Vec<LitVec> {
        self.frame
            .invariant()
            .iter()
            .map(|l| l.map_var(|l| self.rst[l]))
            .collect()
    }
}

impl Engine for IC3 {
    fn check(&mut self) -> Option<bool> {
        if !self.base() {
            return Some(false);
        }
        loop {
            let start = Instant::now();
            debug!("blocking phase begin");
            loop {
                match self.block() {
                    Some(false) => {
                        self.statistic.block.overall_time += start.elapsed();
                        return Some(false);
                    }
                    None => {
                        self.statistic.block.overall_time += start.elapsed();
                        self.verify();
                        return Some(true);
                    }
                    _ => (),
                }
                if let Some((bad, inputs, depth)) = self.get_bad() {
                    debug!("bad state found in last frame");
                    let bad = LitOrdVec::new(bad);
                    self.add_obligation(ProofObligation::new(
                        self.level(),
                        bad,
                        inputs,
                        depth,
                        None,
                    ))
                } else {
                    break;
                }
            }
            debug!("blocking phase end");
            let blocked_time = start.elapsed();
            self.filog.log(Level::Info, self.frame.statistic(true));
            self.statistic.block.overall_time += blocked_time;
            self.extend();
            let start = Instant::now();
            let propagate = self.propagate(None);
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
                self.verify();
                return Some(true);
            }
            self.propagete_to_inf();
        }
    }

    fn proof(&mut self) -> Proof {
        let invariants = self.frame.invariant();
        let invariants = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().filter_map(|l| self.rst.lit_map(*l))));
        let mut proof = self.ots.clone();
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf.push(proof.rel.new_and(cube));
        }
        let invariants = proof.rel.new_or(certifaiger_dnf);
        let constrains: Vec<_> = proof
            .constraint
            .iter()
            .map(|e| !*e)
            .chain(proof.bad.iter().copied())
            .collect();
        let constrains = proof.rel.new_or(constrains);
        proof.bad = LitVec::from(proof.rel.new_or([invariants, constrains]));
        Proof { proof }
    }

    fn witness(&mut self) -> Witness {
        let mut res = Witness::default();
        if let Some((bmc_solver, uts)) = self.bmc_solver.as_mut() {
            for k in 0..=uts.num_unroll {
                let mut w = LitVec::new();
                for l in uts.ts.input() {
                    let l = l.lit();
                    let kl = uts.lit_next(l, k);
                    if let Some(v) = bmc_solver.sat_value(kl)
                        && let Some(r) = self.rst.lit_map(l.not_if(!v))
                    {
                        w.push(r);
                    }
                }
                res.input.push(w);
                let mut w = LitVec::new();
                for l in uts.ts.latch() {
                    let l = l.lit();
                    let kl = uts.lit_next(l, k);
                    if let Some(v) = bmc_solver.sat_value(kl)
                        && let Some(r) = self.rst.lit_map(l.not_if(!v))
                    {
                        w.push(r);
                    }
                }
                res.state.push(w);
            }
            return res;
        }
        let b = self.obligations.peak().unwrap();
        assert!(b.frame == 0);
        let mut b = Some(b);
        while let Some(bad) = b {
            if bad.frame == 0 {
                let assump: Vec<_> = bad
                    .lemma
                    .iter()
                    .chain(bad.input[0].iter())
                    .filter_map(|l| self.rst.lit_map(*l))
                    .collect();
                let (input, state) = self.ots.exact_init_state(&assump);
                res.state.push(state);
                res.input.push(input);
                for i in bad.input[1..].iter() {
                    res.input
                        .push(i.iter().filter_map(|l| self.rst.lit_map(*l)).collect());
                }
            } else {
                res.state.push(
                    bad.lemma
                        .iter()
                        .filter_map(|l| self.rst.lit_map(*l))
                        .collect(),
                );
                for i in bad.input.iter() {
                    res.input
                        .push(i.iter().filter_map(|l| self.rst.lit_map(*l)).collect());
                }
            }
            b = bad.next.clone();
        }
        res
    }

    fn statistic(&mut self) {
        self.statistic.num_auxiliary_var = self.auxiliary_var.len();
        info!("obligations: {}", self.obligations.statistic());
        info!("{}", self.frame.statistic(false));
        let mut statistic = SolverStatistic::default();
        for s in self.solvers.iter() {
            statistic += *s.statistic();
        }
        info!("{statistic:#?}");
        info!("{:#?}", self.statistic);
    }
}
