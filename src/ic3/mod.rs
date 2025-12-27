use crate::{
    BlProof, BlWitness, Engine, McProof, McResult, McWitness,
    config::{EngineConfig, EngineConfigBase, PreprocConfig},
    gipsat::{SolverStatistic, TransysSolver},
    ic3::{block::BlockResult, localabs::LocalAbs, predprop::PredProp},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    transys::{
        Transys, TransysCtx, TransysIf, certify::Restore, lift::TsLift, unroll::TransysUnroll,
    },
};
use activity::Activity;
use clap::{ArgAction, Args, Parser};
use frame::{Frame, Frames};
use giputils::{grc::Grc, logger::IntervalLogger};
use log::{Level, debug, error, info, trace};
use logicrs::{Lit, LitOrdVec, LitVec, LitVvec, Var, VarSymbols, satif::Satif};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};
use std::{
    sync::{Arc, atomic::AtomicBool},
    time::Instant,
};
use utils::Statistic;

mod activity;
mod aux;
mod block;
mod frame;
mod localabs;
mod mic;
mod predprop;
mod proofoblig;
mod propagate;
mod solver;
mod utils;

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct IC3Config {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,

    /// dynamic generalization
    #[arg(long = "dynamic", default_value_t = false)]
    pub dynamic: bool,

    /// counterexample to generalization
    #[arg(long = "ctg", action = ArgAction::Set, default_value_t = true)]
    pub ctg: bool,

    /// max number of ctg
    #[arg(long = "ctg-max", default_value_t = 3)]
    pub ctg_max: usize,

    /// ctg limit
    #[arg(long = "ctg-limit", default_value_t = 1)]
    pub ctg_limit: usize,

    /// counterexample to propagation
    #[arg(long = "ctp", default_value_t = false)]
    pub ctp: bool,

    /// internal signals (FMCAD'21 https://doi.org/10.34727/2021/isbn.978-3-85448-046-4_14)
    #[arg(long = "inn", default_value_t = false)]
    pub inn: bool,

    /// abstract constrains
    #[arg(long = "abs-cst", default_value_t = false)]
    pub abs_cst: bool,

    /// abstract trans
    #[arg(long = "abs-trans", default_value_t = false)]
    pub abs_trans: bool,

    /// dropping proof-obligation
    #[arg(
        long = "drop-po", action = ArgAction::Set, default_value_t = true,
    )]
    pub drop_po: bool,

    /// full assignment of last bad (used in rlive)
    #[arg(long = "full-bad", default_value_t = false)]
    pub full_bad: bool,

    /// abstract array
    #[arg(long = "abs-array", default_value_t = false)]
    pub abs_array: bool,

    /// finding parent lemma in mic (CAV'23 https://doi.org/10.1007/978-3-031-37703-7_14)
    #[arg(long = "parent-lemma", action = ArgAction::Set, default_value_t = true)]
    pub parent_lemma: bool,

    /// predicate property
    #[arg(long = "pred-prop", default_value_t = false)]
    pub pred_prop: bool,

    /// local proof (can only used in multi-prop)
    #[arg(long = "local-proof", default_value_t = false)]
    pub local_proof: bool,
}

impl_config_deref!(IC3Config);

impl Default for IC3Config {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "ic3"]);
        cfg.into_ic3().unwrap()
    }
}

impl IC3Config {
    fn validate(&self) {
        if self.dynamic && self.drop_po {
            error!("cannot enable both dynamic and drop-po");
            panic!();
        }
        if self.inn {
            let pre = "cannot enable both inn and";
            if self.abs_cst || self.abs_trans {
                error!("{pre} (abs_cst or abs_trans)");
                panic!();
            }
        }
        if self.full_bad {
            error!("full-bad can't be used now");
            panic!();
        }
        if self.local_proof {
            if !self.pred_prop {
                error!("local-proof should used with pred-prop");
                panic!();
            }
            if self.prop.is_none() {
                error!("A property ID must be specified for local proof.");
                panic!();
            }
        }
    }
}

pub struct IC3 {
    cfg: IC3Config,
    ts: Transys,
    #[allow(unused)]
    symbols: VarSymbols,
    tsctx: Grc<TransysCtx>,
    solvers: Vec<TransysSolver>,
    inf_solver: TransysSolver,
    lift: TsLift,
    frame: Frames,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    localabs: LocalAbs,
    ots: Transys,
    rst: Restore,
    auxiliary_var: Vec<Var>,
    predprop: Option<PredProp>,

    rng: StdRng,
    filog: IntervalLogger,
    tracer: Tracer,
    stop_ctrl: Arc<AtomicBool>,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        let nl = self.solvers.len();
        debug!("extending IC3 to level {nl}");
        if let Some(predprop) = self.predprop.as_mut() {
            predprop.extend(self.frame.inf.iter().map(|l| l.cube()));
        }
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
}

impl IC3 {
    pub fn new(cfg: IC3Config, mut ts: Transys, symbols: VarSymbols) -> Self {
        cfg.validate();
        let ots = ts.clone();
        if let Some(prop) = cfg.prop {
            if !cfg.local_proof {
                ts.bad = LitVec::from(ts.bad[prop]);
            }
        } else {
            ts.compress_bads();
        }
        let rst = Restore::new(&ts);
        let rng = StdRng::seed_from_u64(cfg.rseed);
        let statistic = Statistic::default();
        let (mut ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        ts.remove_gate_init(&mut rst);
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if cfg.inn {
            ts = uts.interal_signals();
        }
        let predprop = cfg.pred_prop.then(|| {
            PredProp::new(
                uts.clone(),
                cfg.local_proof.then(|| cfg.prop.unwrap()),
                cfg.inn,
            )
        });
        let tsctx = Grc::new(ts.ctx());
        let activity = Activity::new(&tsctx);
        let frame = Frames::new(&tsctx);
        let inf_solver = TransysSolver::new(&tsctx);
        let lift = TsLift::new(TransysUnroll::new(&ts));
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
            predprop,
            rng,
            filog: Default::default(),
            tracer: Tracer::new(),
            stop_ctrl: Arc::new(AtomicBool::new(false)),
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
    fn check(&mut self) -> McResult {
        self.extend();
        if !self.prep_prop_base() {
            self.tracer.trace_res(McResult::Unsafe(0));
            return McResult::Unsafe(0);
        }
        loop {
            let start = Instant::now();
            debug!("blocking phase begin");
            loop {
                match self.block(None) {
                    BlockResult::Failure(depth) => {
                        self.statistic.block.overall_time += start.elapsed();
                        self.tracer.trace_res(McResult::Unsafe(depth));
                        return McResult::Unsafe(depth);
                    }
                    BlockResult::Proved => {
                        self.statistic.block.overall_time += start.elapsed();
                        self.tracer.trace_res(McResult::Safe);
                        return McResult::Safe;
                    }
                    BlockResult::OverallTimeLimitExceeded => {
                        self.statistic.block.overall_time += start.elapsed();
                        return McResult::Unknown(Some(self.level()));
                    }
                    _ => (),
                }
                if let Some((bad, inputs)) = self.get_bad() {
                    debug!("bad state found in frame {}", self.level());
                    trace!("bad = {bad}");
                    let bad = LitOrdVec::new(bad);
                    let depth = inputs.len() - 1;
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
            self.statistic.block.overall_time += start.elapsed();
            self.filog.log(Level::Info, self.frame.statistic(true));
            self.tracer.trace_res(McResult::Unknown(Some(self.level())));
            self.extend();
            let start = Instant::now();
            let propagate = self.propagate(None);
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
                self.tracer.trace_res(McResult::Safe);
                return McResult::Safe;
            }
            self.propagete_to_inf();
        }
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn proof(&mut self) -> McProof {
        let mut proof = self.ots.clone();
        if let Some(iv) = self.rst.init_var() {
            let piv = proof.add_init_var();
            self.rst.add_restore(iv, piv);
        }
        let mut invariants = self.frame.invariant();
        for c in self.ts.constraint.clone() {
            proof
                .rel
                .migrate(&self.ts.rel, c.var(), &mut self.rst.bvmap);
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
        McProof::Bl(BlProof { proof })
    }

    fn witness(&mut self) -> McWitness {
        let mut res = if let Some(res) = self.localabs.witness() {
            res
        } else {
            let mut res = BlWitness::default();
            let b = self.obligations.peak().unwrap();
            assert!(b.frame == 0);
            let mut b = Some(b);
            while let Some(bad) = b {
                res.state.push(bad.state.cube().clone());
                res.input.push(bad.input[0].clone());
                for i in &bad.input[1..] {
                    res.input.push(i.clone());
                    res.state.push(LitVec::new());
                }
                b = bad.next.clone();
            }
            res
        };
        let iv = self.rst.init_var();
        res = res.filter_map(|l| {
            (iv != Some(l.var()))
                .then(|| self.rst.try_restore(l))
                .flatten()
        });
        for s in res.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        res.exact_state(&self.ots);
        McWitness::Bl(res)
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

    fn get_stop_ctrl(&self) -> Arc<AtomicBool> {
        self.stop_ctrl.clone()
    }
}
