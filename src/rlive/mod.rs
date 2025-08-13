use crate::{
    Engine, Witness,
    config::Config,
    ic3::IC3,
    transys::{Transys, TransysIf},
};
use clap::Parser;
use log::{debug, error, warn};
use logicrs::{Lit, LitOrdVec, LitVec, Var, VarVMap};
use std::mem::take;

pub struct Rlive {
    #[allow(unused)]
    cfg: Config,
    ts: Transys,
    rcfg: Config,  // reach check config
    rts: Transys,  // reach check ts
    base_var: Var, // base var
    trace: Vec<LitOrdVec>,
    witness: Vec<Witness>,
    shoals: Vec<LitVec>,
    rst: VarVMap,
}

impl Rlive {
    #[inline]
    fn level(&self) -> usize {
        assert!(self.trace.len() == self.witness.len());
        self.trace.len()
    }

    #[inline]
    fn add_trace(&mut self, mut w: Witness) -> bool {
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

    fn check_reach(&mut self, s: LitVec) -> Result<Vec<LitVec>, Witness> {
        let mut rts = self.rts.clone();
        for l in s {
            assert!(l.var() != self.base_var);
            rts.init.insert(l.var(), Lit::constant(l.polarity()));
        }
        let mut ic3 = IC3::new(self.rcfg.clone(), rts);
        if ic3.check().unwrap() {
            return Ok(ic3.invariant());
        }
        let wit = ic3.witness();
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
    pub fn new(cfg: Config, mut ts: Transys) -> Self {
        warn!("rlive is unstable, use with caution");
        if ts.justice.is_empty() {
            error!("rlive requires justice property");
            panic!();
        }
        let mut rst = VarVMap::new_self_map(ts.max_var());
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
            Config::parse_from("-e ic3 --no-ic3-pred-prop --ic3-full-bad --no-preproc".split(' '));
        Self {
            cfg,
            ts,
            rcfg,
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
    fn check(&mut self) -> Option<bool> {
        loop {
            let mut ts = self.ts.clone();
            ts.bad = take(&mut ts.justice);
            let mut ic3 = IC3::new(self.rcfg.clone(), ts);
            if ic3.check().unwrap() {
                return Some(true);
            }
            let wit = ic3.witness();
            assert!(self.level() == 0);
            self.add_trace(wit);
            if !self.block() {
                return Some(false);
            }
        }
    }

    fn witness(&mut self) -> Witness {
        let witness = Witness::concat(self.witness.clone());
        witness.filter_map_var(|v| self.rst.get(&v).copied())
    }
}
