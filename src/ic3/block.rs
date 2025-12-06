use crate::ic3::{
    IC3,
    mic::{DropVarParameter, MicType},
    proofoblig::ProofObligation,
};
use log::{debug, info};
use logicrs::{LitOrdVec, LitVec, satif::Satif};
use std::time::Instant;

pub enum BlockResult {
    Success,
    Failure,
    Proved,
    BlockLimitExceeded,
    OverallTimeLimitExceeded,
}

impl IC3 {
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
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.state.cube().clone(), false, Some(po));
        };
        mic = self.mic(po.frame, mic, &[], mic_type);
        let (frame, mic) = self.push_lemma(po.frame, mic);
        self.statistic.avg_po_cube_len += po.state.len();
        po.push_to(frame);
        self.add_obligation(po.clone());
        debug!(
            "generalized lemma {:?} in F{}",
            self.lits_symbols(mic.clone()),
            frame - 1
        );
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
                BlockResult::BlockLimitExceeded => {
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

    pub fn block(&mut self, limit: Option<f64>) -> BlockResult {
        let mut noc = 0;
        while let Some(mut po) = self.obligations.pop(self.level()) {
            if po.removed {
                continue;
            }
            if let Some(limit) = limit
                && noc as f64 > limit
            {
                return BlockResult::BlockLimitExceeded;
            }
            if let Some(limit) = self.cfg.time_limit
                && self.statistic.time.time().as_secs() > limit
            {
                return BlockResult::OverallTimeLimitExceeded;
            }
            if self.tsctx.cube_subsume_init(&po.state) {
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
                    let lemma = po.state.cube();
                    debug_assert!(!self.solvers[0].solve(lemma));
                } else {
                    self.add_obligation(po.clone());
                    return BlockResult::Failure;
                }
            }
            if let Some((bf, _)) = self.frame.trivial_contained(Some(po.frame), &po.state) {
                if let Some(bf) = bf {
                    po.push_to(bf + 1);
                    self.add_obligation(po);
                }
                continue;
            }
            po.bump_act();
            if self.cfg.ic3.drop_po && po.act > 20.0 {
                continue;
            }
            let blocked_start = Instant::now();
            let blocked = self.blocked_with_ordered(po.frame, &po.state, false);
            self.statistic.block.blocked_time += blocked_start.elapsed();
            if blocked {
                debug!(
                    "blocked {:?} in F{} with depth {}",
                    self.lits_symbols(po.state.clone()),
                    po.frame,
                    po.depth
                );
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
                                let limit = ((act - EXCTG_THRESHOLD).powf(0.45) * 2.0 + 5.0).round()
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
                debug!("{}", self.frame.statistic(false));
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

    pub fn trivial_block(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> bool {
        let mut limit = parameter.limit;
        self.trivial_block_rec(frame, lemma, constraint, &mut limit, parameter)
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
