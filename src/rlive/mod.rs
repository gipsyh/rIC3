use crate::{
    BlWitness, Engine, McResult, McWitness,
    config::{EngineConfig, EngineConfigBase, PreprocConfig},
    ic3::{IC3, IC3Config},
    transys::{Transys, TransysIf, certify::Restore},
};
use clap::{Args, Parser};
use log::{LevelFilter, debug, error, warn};
use logicrs::{Lit, LitOrdVec, LitVec, Var, VarSymbols};
use serde::{Deserialize, Serialize};
use std::{mem::take, ops::Deref};

pub struct Rlive {
    #[allow(unused)]
    cfg: RliveConfig,
    ts: Transys,
    rcfg: IC3Config, // reach check config
    rts: Transys,    // reach check ts
    base_var: Var,   // base var
    trace: Vec<LitOrdVec>,
    witness: Vec<BlWitness>,
    shoals: Vec<LitVec>,
    rst: Restore,
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct RliveConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,
}

impl Deref for RliveConfig {
    type Target = EngineConfigBase;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

impl Rlive {
    #[inline]
    fn level(&self) -> usize {
        assert!(self.trace.len() == self.witness.len());
        self.trace.len()
    }

    #[inline]
    fn add_trace(&mut self, mut w: BlWitness) -> bool {
        for s in w.state.iter_mut().chain(w.input.iter_mut()) {
            s.retain(|l| l.var() != self.base_var);
        }
        let s = LitOrdVec::new(w.state.pop().unwrap());
        w.input.pop();
        self.witness.push(w);
        for t in self.trace.iter() {
            if t.subsume(&s) || s.subsume(t) {
                self.trace.push(s);
                return false;
            }
        }
        self.trace.push(s);
        true
    }

    fn add_shoal(&mut self, mut shoal: Vec<LitVec>) {
        shoal.retain(|s| s.iter().all(|l| l.var() != self.base_var));
        let ors: Vec<_> = shoal
            .iter()
            .map(|s| self.rts.rel.new_and(s.clone()))
            .collect();
        let c = self.rts.rel.new_or(ors);
        self.rts.constraint.push(c);
        let ors: Vec<_> = shoal
            .iter()
            .map(|s| self.ts.rel.new_and(s.clone()))
            .collect();
        let c = self.ts.rel.new_or(ors);
        self.ts.constraint.push(c);
        self.shoals.extend(shoal);
    }

    #[inline]
    fn pop_trace(&mut self) {
        self.trace.pop();
        self.witness.pop();
    }

    fn check_reach(&mut self, s: LitVec) -> Result<Vec<LitVec>, BlWitness> {
        let mut rts = self.rts.clone();
        for l in s {
            assert!(l.var() != self.base_var);
            rts.init.insert(l.var(), Lit::constant(l.polarity()));
        }
        let mut ic3 = IC3::new(self.rcfg.clone(), rts, VarSymbols::new());
        let prev_level = log::max_level();
        log::set_max_level(LevelFilter::Warn);
        let res = ic3.check();
        log::set_max_level(prev_level);
        if let McResult::Safe = res {
            return Ok(ic3.invariant());
        }
        let wit = ic3.witness().into_bl().unwrap();
        assert!(wit.input.len() > 1);
        Err(wit)
    }

    fn block(&mut self) -> bool {
        loop {
            debug!("rlive block at level {}", self.level());
            let s = self.trace.last().unwrap().clone();
            match self.check_reach(s.cube().clone()) {
                Ok(inv) => {
                    self.add_shoal(inv);
                    self.pop_trace();
                    return true;
                }
                Err(b) => {
                    if self.add_trace(b) {
                        if !self.block() {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
            }
        }
    }
}

impl Rlive {
    pub fn new(cfg: RliveConfig, mut ts: Transys) -> Self {
        warn!("rlive is unstable, use with caution");
        if ts.justice.is_empty() {
            error!("rlive requires justice property");
            panic!();
        }
        let mut rst = Restore::new(&ts);
        ts.normalize_justice();
        if cfg.preproc.preproc {
            ts.simplify(&mut rst);
        }
        assert!(ts.justice.len() == 1);
        let base_var = ts.new_var();
        ts.add_latch(base_var, Some(Lit::constant(false)), Lit::constant(true));
        let mut rts = ts.clone();
        rts.init.clear();
        rts.add_init(base_var, Lit::constant(false));
        rts.bad = take(&mut rts.justice);
        let bvc = rts.rel.new_imply(!base_var.lit(), rts.bad[0]);
        rts.constraint.push(bvc);
        rts.bad = LitVec::from(rts.rel.new_and([rts.bad[0], base_var.lit()]));
        let rcfg =
            EngineConfig::parse_from("ic3 --no-pred-prop --full-bad --no-preproc".split(' '));
        let rcfg = rcfg.into_ic3().unwrap();
        Self {
            cfg,
            ts,
            rcfg: rcfg.clone(),
            rts,
            base_var,
            trace: Vec::new(),
            witness: Vec::new(),
            shoals: Vec::new(),
            rst,
        }
    }
}

impl Engine for Rlive {
    fn check(&mut self) -> McResult {
        loop {
            let mut ts = self.ts.clone();
            ts.bad = take(&mut ts.justice);
            let mut ic3 = IC3::new(self.rcfg.clone(), ts, VarSymbols::new());
            let prev_level = log::max_level();
            log::set_max_level(LevelFilter::Warn);
            let res = ic3.check();
            log::set_max_level(prev_level);
            if let McResult::Safe = res {
                return McResult::Safe;
            }
            let wit = ic3.witness().into_bl().unwrap();
            assert!(self.level() == 0);
            self.add_trace(wit);
            if !self.block() {
                return McResult::Unsafe(0);
            }
        }
    }

    fn witness(&mut self) -> McWitness {
        let witness = BlWitness::concat(self.witness.clone());
        McWitness::Bl(witness.map_var(|v| self.rst.restore_var(v)))
    }
}
