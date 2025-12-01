use crate::{
    Engine, Proof, Witness,
    config::Config,
    gipsat::{SolverStatistic, TransysSolver},
    ic3::{block::BlockResult, localabs::LocalAbs},
    transys::{Transys, TransysCtx, TransysIf, certify::Restore, unroll::TransysUnroll},
};
use activity::Activity;
use frame::{Frame, Frames};
use giputils::{grc::Grc, logger::IntervalLogger};
use log::{Level, debug, info, trace};
use logicrs::{Lit, LitOrdVec, LitVec, LitVvec, Var, VarSymbols, satif::Satif};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::time::Instant;
use utils::Statistic;

mod activity;
mod aux;
mod block;
mod frame;
mod localabs;
mod mic;
mod proofoblig;
mod propagate;
mod solver;
mod utils;
mod verify;

pub struct IC3 {
    cfg: Config,
    ts: Transys,
    symbols: VarSymbols,
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
    rst: Restore,
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
        let nl = self.solvers.len();
        debug!("extending IC3 to level {nl}");
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
    pub fn new(cfg: Config, mut ts: Transys, symbols: VarSymbols) -> Self {
        let ots = ts.clone();
        ts.compress_bads();
        let rst = Restore::new(&ts);
        let mut rng = StdRng::seed_from_u64(cfg.rseed);
        let statistic = Statistic::default();
        let (mut ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if cfg.ic3.inn {
            ts = uts.interal_signals();
        }
        ts.remove_gate_init(&mut rst);
        let tsctx = Grc::new(ts.ctx());
        let activity = Activity::new(&tsctx);
        let frame = Frames::new(&tsctx);
        let mut inf_solver = TransysSolver::new(&tsctx, true);
        inf_solver.dcs.set_rseed(rng.random());
        let lift = TransysSolver::new(&tsctx, false);
        let localabs = LocalAbs::new(&ts, &cfg);
        Self {
            cfg,
            ts,
            symbols,
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
            .map(|l| l.map_var(|l| self.rst.restore_var(l)))
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
                    debug!("bad state found in frame {}", self.level());
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
        let mut proof = self.ots.clone();
        if let Some(iv) = self.rst.init_var() {
            let piv = proof.add_init_var();
            self.rst.add_restore(iv, piv);
        }
        let mut invariants = self.frame.invariant();
        for c in self.ts.constraint.clone() {
            proof.rel.migrate(&self.ts.rel, c.var(), &mut self.rst.vmap);
            invariants.push(LitVec::from(!c));
        }
        let mut invariants: LitVvec = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().map(|l| self.rst.restore(*l))))
            .collect();
        invariants.extend(self.rst.eq_invariant());
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf.push(proof.rel.new_and(cube));
        }
        let invariants = proof.rel.new_or(certifaiger_dnf);
        let bad = proof.rel.new_or(proof.bad);
        proof.bad = LitVec::from(proof.rel.new_or([invariants, bad]));
        Proof { proof }
    }

    fn witness(&mut self) -> Witness {
        let mut res = if let Some(res) = self.localabs.witness() {
            res
        } else {
            let mut res = Witness::default();
            let b = self.obligations.peak().unwrap();
            assert!(b.frame == 0);
            let mut b = Some(b);
            while let Some(bad) = b {
                res.state.push(bad.state.iter().cloned().collect());
                res.input.push(bad.input.iter().cloned().collect());
                b = bad.next.clone();
            }
            res
        };
        let iv = self.rst.init_var();
        res.filter_map(|l| (iv != Some(l.var())).then(|| self.rst.restore(l)));
        for s in res.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        res.exact_state(&self.ots);
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
