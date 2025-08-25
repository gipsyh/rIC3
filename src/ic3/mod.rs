use crate::{
    Engine, Proof, Witness,
    config::Config,
    gipsat::{SolverStatistic, TransysSolver},
    ic3::{block::BlockResult, localabs::LocalAbs},
    transys::{Transys, TransysCtx, TransysIf, frts::FrTs, scorr::Scorr, unroll::TransysUnroll},
};
use activity::Activity;
use frame::{Frame, Frames};
use giputils::{grc::Grc, hash::GHashMap, logger::IntervalLogger};
use log::{Level, debug, info, trace};
use logicrs::{Lit, LitOrdVec, LitVec, Var, VarVMap, satif::Satif};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{SeedableRng, rngs::StdRng};
use statistic::Statistic;
use std::time::Instant;

mod activity;
mod aux;
mod block;
mod frame;
mod localabs;
mod mic;
mod proofoblig;
mod propagate;
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

    fn base(&mut self) -> bool {
        self.extend();
        assert!(self.level() == 0);
        true
    }
}

impl IC3 {
    pub fn new(cfg: Config, mut ts: Transys) -> Self {
        let ots = ts.clone();
        let rng = StdRng::seed_from_u64(cfg.rseed);
        let mut rst = VarVMap::new_self_map(ts.max_var());
        ts = ts.check_liveness_and_l2s(&mut rst);
        let statistic = Statistic::default();
        if cfg.preproc.preproc {
            ts.simplify(&mut rst);
            info!("trivial simplified ts: {}", ts.statistic());
            if cfg.preproc.scorr {
                let scorr = Scorr::new(ts, &cfg, rst);
                (ts, rst) = scorr.scorr();
            }
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
        let tsctx = Grc::new(ts.ctx());
        let activity = Activity::new(&tsctx);
        let frame = Frames::new(&tsctx);
        let inf_solver = TransysSolver::new(&tsctx, true);
        let lift = TransysSolver::new(&tsctx, false);
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
