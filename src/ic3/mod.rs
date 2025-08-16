use crate::{
    Engine, Proof, Witness,
    config::Config,
    gipsat::{SolverStatistic, TransysSolver},
    ic3::{frame::FrameLemma, localabs::LocalAbs},
    transys::{Transys, TransysCtx, TransysIf, frts::FrTs, unroll::TransysUnroll},
};
use activity::Activity;
use frame::{Frame, Frames};
use giputils::{grc::Grc, hash::GHashMap, logger::IntervalLogger};
use log::{Level, debug, info, trace};
use logicrs::{Lit, LitOrdVec, LitVec, Var, VarVMap, satif::Satif};
use mic::{DropVarParameter, MicType};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{Rng, SeedableRng, rngs::StdRng, seq::SliceRandom};
use statistic::Statistic;
use std::time::Instant;

mod activity;
mod aux;
mod frame;
mod localabs;
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
    frame: Frames,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    localabs: LocalAbs,
    ots: Transys,
    rst: VarVMap,
    auxiliary_var: Vec<Var>,
    rng: StdRng,

    filog: IntervalLogger,
}

enum BlockResult {
    Success,
    Failure,
    Proved,
    LimitExceeded,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        debug!("extending IC3 to level {}", self.solvers.len());
        let solver = self.inf_solver.clone();
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
        }
    }

    fn push_lemma(&mut self, frame: usize, mut cube: LitVec) -> (usize, LitVec) {
        let start = Instant::now();
        for i in frame + 1..=self.level() {
            if self.solvers[i - 1].inductive(&cube, true) {
                cube = self.solvers[i - 1].inductive_core().unwrap_or(cube);
            } else {
                return (i, cube);
            }
        }
        self.statistic.block.push_time += start.elapsed();
        (self.level() + 1, cube)
    }

    fn generalize(&mut self, mut po: ProofObligation, mic_type: MicType) -> bool {
        let Some(mut mic) = self.solvers[po.frame - 1].inductive_core() else {
            assert!(self.tsctx.cube_subsume_init(&po.lemma));
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.lemma.cube().clone(), false, Some(po));
        };
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

    #[allow(unused)]
    fn block_with_restart(&mut self) -> BlockResult {
        let mut restart = 0;
        loop {
            let rest_base = luby(2.0, restart);
            match self.block(Some(rest_base * 100.0)) {
                BlockResult::LimitExceeded => {
                    let bt = if let Some(a) = self.obligations.peak() {
                        (a.frame + 2).min(self.level() - 1)
                    } else {
                        self.level() - 1
                    };
                    self.obligations.clear_to(bt);
                    restart += 1;
                    if restart % 10 == 0 {
                        info!("rIC3 restarted {restart} times");
                    }
                }
                r => return r,
            }
        }
    }

    fn block(&mut self, limit: Option<f64>) -> BlockResult {
        let mut noc = 0;
        while let Some(mut po) = self.obligations.pop(self.level()) {
            if po.removed {
                continue;
            }
            if let Some(limit) = limit
                && noc as f64 > limit
            {
                return BlockResult::LimitExceeded;
            }
            debug!(
                "blocking {} in frame {} with depth {}",
                po.lemma, po.frame, po.depth
            );
            if self.tsctx.cube_subsume_init(&po.lemma) {
                if self.cfg.ic3.abs_cst || self.cfg.ic3.abs_trans {
                    self.add_obligation(po.clone());
                    if self.check_witness_by_bmc(po.depth) {
                        return BlockResult::Failure;
                    } else {
                        self.obligations.clear();
                        for f in self.frame.iter_mut() {
                            for l in f.iter_mut() {
                                l.po = None;
                            }
                        }
                        continue;
                    }
                } else if po.frame > 0 {
                    let mut assump = po.lemma.cube().clone();
                    assump.extend(po.input.iter());
                    debug_assert!(!self.solvers[0].solve(&assump));
                } else {
                    self.add_obligation(po.clone());
                    return BlockResult::Failure;
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
            if self.cfg.ic3.drop_po && po.act > 10.0 {
                continue;
            }
            let blocked_start = Instant::now();
            let blocked = self.blocked_with_ordered(po.frame, &po.lemma, false, false);
            self.statistic.block.blocked_time += blocked_start.elapsed();
            if blocked {
                noc += 1;
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
                    return BlockResult::Proved;
                }
            } else {
                let (model, inputs) = self.get_pred(po.frame, true);
                self.add_obligation(ProofObligation::new(
                    po.frame - 1,
                    LitOrdVec::new(model),
                    inputs,
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.add_obligation(po);
            }
        }
        BlockResult::Success
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
                let mut mic = self.solvers[frame - 1].inductive_core().unwrap();
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
                        let core = self.solvers[frame_idx]
                            .inductive_core()
                            .unwrap_or(lemma.cube().clone());
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
                        let core = self.solvers[frame_idx - 1].inductive_core().unwrap();
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
        true
    }
}

impl IC3 {
    pub fn new(cfg: Config, mut ts: Transys) -> Self {
        let ots = ts.clone();
        let mut rng = StdRng::seed_from_u64(cfg.rseed);
        let mut rst = VarVMap::new_self_map(ts.max_var());
        ts = ts.check_liveness_and_l2s(&mut rst);
        let statistic = Statistic::default();
        if cfg.preproc.preproc {
            ts.simplify(&mut rst);
            if cfg.preproc.frts {
                let frts = FrTs::new(ts, &cfg, rst);
                (ts, rst) = frts.fr();
            }
        }
        info!("simplified ts has {}", ts.statistic());

        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if cfg.ic3.inn {
            ts = uts.interal_signals();
        }
        let mut bad_input = GHashMap::new();
        for &l in ts.input.iter() {
            let n = uts.var_next(l, 1);
            bad_input.insert(n, l);
        }
        for l in ts.latch_no_next() {
            let n = uts.var_next(l, 1);
            bad_input.insert(n, l);
        }
        let tsctx = Grc::new(ts.ctx());
        let activity = Activity::new(&tsctx);
        let frame = Frames::new(&tsctx);
        let inf_solver = TransysSolver::new(&tsctx, true, rng.random());
        let lift = TransysSolver::new(&tsctx, false, rng.random());
        let localabs = LocalAbs::new(&ts, &cfg);
        Self {
            cfg,
            ts,
            tsctx,
            activity,
            solvers: Vec::new(),
            inf_solver,
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
            localabs,
            auxiliary_var: Vec::new(),
            ots,
            rst,
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
                match self.block(None) {
                    BlockResult::Failure => {
                        self.statistic.block.overall_time += start.elapsed();
                        return Some(false);
                    }
                    BlockResult::Proved => {
                        self.statistic.block.overall_time += start.elapsed();
                        self.verify();
                        return Some(true);
                    }
                    _ => (),
                }
                if let Some((bad, inputs)) = self.get_bad() {
                    debug!("bad state found in last frame");
                    trace!("bad = {bad}");
                    let bad = LitOrdVec::new(bad);
                    self.add_obligation(ProofObligation::new(self.level(), bad, inputs, 0, None))
                } else {
                    break;
                }
            }
            debug!("blocking phase end");
            self.statistic.block.overall_time += start.elapsed();
            self.filog.log(Level::Info, self.frame.statistic(true));
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
        if let Some(res) = self.localabs.witness(&self.rst) {
            return res;
        }
        let mut res = Witness::default();
        let b = self.obligations.peak().unwrap();
        assert!(b.frame == 0);
        let mut b = Some(b);
        while let Some(bad) = b {
            if bad.frame == 0 {
                let assump: Vec<_> = bad
                    .lemma
                    .iter()
                    .chain(bad.input.iter())
                    .filter_map(|l| self.rst.lit_map(*l))
                    .collect();
                let (input, state) = self.ots.exact_init_state(&assump);
                res.state.push(state);
                res.input.push(input);
            } else {
                res.state.push(
                    bad.lemma
                        .iter()
                        .filter_map(|l| self.rst.lit_map(*l))
                        .collect(),
                );
                res.input.push(
                    bad.input
                        .iter()
                        .filter_map(|l| self.rst.lit_map(*l))
                        .collect(),
                );
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

fn luby(y: f64, mut x: usize) -> f64 {
    let mut size = 1;
    let mut seq = 0;
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1
    }
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    y.powi(seq)
}
