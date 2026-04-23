use crate::{
    gipsat::TransysSolver,
    ic3::{IC3, frame::FrameLemma, mic::MicType},
    transys::TransysIf,
};
use logicrs::{LitOrdVec, LitVec, satif::Satif};
use rand::seq::SliceRandom;
use std::time::Instant;

impl IC3 {
    pub fn propagate(&mut self, from: Option<usize>) -> bool {
        let level = self.level();
        let from = from.unwrap_or(self.frame.early).max(1);
        for frame_idx in from..level {
            let mut frame = self.frame[frame_idx].clone();
            frame.sort_by_key(|x| x.len());
            for mut lemma in frame {
                if self.frame[frame_idx].iter().all(|l| l.ne(&lemma)) {
                    continue;
                }
                for ctp in 0..3 {
                    if self
                        .blocked(frame_idx + 1, &lemma)
                        .with_act_order(false)
                        .check()
                    {
                        let core = self.solvers[frame_idx]
                            .inductive_core()
                            .unwrap_or(lemma.as_litvec().clone());
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
                    if !self.cfg.ctp {
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

    pub fn propagete_to_inf_rec(&mut self, lastf: &mut Vec<FrameLemma>, ctp: LitVec) -> bool {
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
                self.add_inf_lemma(lemma.as_litvec().clone());
                return true;
            } else {
                let target = self.tsctx.lits_next(lemma.as_litvec());
                let (ctp, _) = self.lift.lift(
                    &mut self.inf_solver,
                    target.iter().chain(self.tsctx.constraint.iter()),
                    |i, _| i == 0,
                );
                if !self.propagete_to_inf_rec(lastf, ctp) {
                    return false;
                }
            }
        }
    }

    pub fn propagate_to_inf(&mut self) {
        let start = Instant::now();
        let mut lastf = self.frame.last().clone();
        lastf.shuffle(&mut self.rng);
        while let Some(mut lemma) = lastf.pop() {
            loop {
                if self.inf_solver.inductive(&lemma, true) {
                    if let Some(po) = &mut lemma.po {
                        self.obligations.remove(po);
                    }
                    self.add_inf_lemma(lemma.as_litvec().clone());
                    break;
                } else {
                    let target = self.tsctx.lits_next(lemma.as_litvec());
                    let (ctp, _) = self.lift.lift(
                        &mut self.inf_solver,
                        target.iter().chain(self.tsctx.constraint.iter()),
                        |i, _| i == 0,
                    );
                    if !self.propagete_to_inf_rec(&mut lastf, ctp) {
                        break;
                    }
                }
            }
        }
        self.statistic.propagate.push_inf_time += start.elapsed();
    }

    pub fn propagate_to_inf2(&mut self) {
        let start = Instant::now();
        let iter_max = 7;
        let mut cand: Vec<_> = self
            .frame
            .last()
            .iter()
            .map(|l| l.as_litvec().clone())
            .collect();
        if cand.is_empty() {
            return;
        }
        for k in 0..=iter_max {
            if k == iter_max {
                self.statistic.propagate.push_inf_time += start.elapsed();
                return;
            }
            let mut slv = TransysSolver::new(&self.tsctx);
            for i in self.frame.inf.iter() {
                slv.add_clause(&!i.as_litvec());
            }
            for c in cand.iter() {
                slv.add_clause(&!c);
            }
            let mut new_cand = Vec::new();
            for c in cand.iter() {
                if slv.inductive(c, false) {
                    new_cand.push(c.clone());
                }
            }
            if new_cand.len() == cand.len() {
                break;
            } else {
                cand = new_cand;
            }
        }
        for c in cand {
            self.add_inf_lemma(c);
        }
        self.statistic.propagate.push_inf_time += start.elapsed();
    }
}
