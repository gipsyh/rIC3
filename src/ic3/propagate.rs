use crate::{
    ic3::{IC3, frame::FrameLemma, mic::MicType},
    transys::TransysIf,
};
use logicrs::{LitOrdVec, LitVec};
use rand::seq::SliceRandom;

impl IC3 {
    pub fn propagate(&mut self, from: Option<usize>) -> bool {
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

    pub fn propagete_to_inf(&mut self) {
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
}
