#![allow(non_snake_case)]
#![feature(assert_matches, get_mut_unchecked, format_args_nl)]

mod activity;
mod frame;
mod mic;
mod options;
mod proofoblig;
mod solver;
mod statistic;
mod verify;

use crate::proofoblig::{ProofObligation, ProofObligationQueue};
use crate::statistic::Statistic;
use activity::Activity;
use frame::{Frame, Frames};
use giputils::grc::Grc;
use logic_form::{Cube, Lemma};
pub use options::Options;
use solver::{Ic3Solver, Lift};
use std::panic::{self, AssertUnwindSafe};
use std::process::exit;
use std::time::Instant;
use transys::Transys;

pub struct IC3 {
    options: Options,
    ts: Grc<Transys>,
    frame: Frames,
    solvers: Vec<Ic3Solver>,
    lift: Lift,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
}
impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        self.frame.push(Frame::new());
        self.solvers
            .push(Ic3Solver::new(&self.ts, self.solvers.len()));
        if self.level() == 0 {
            for init in self.ts.init.clone() {
                self.add_lemma(0, Cube::from([!init]), true, None);
            }
        }
    }

    fn push_lemma(&mut self, frame: usize, mut cube: Cube) -> (usize, Cube) {
        for i in frame + 1..=self.level() {
            if self.blocked(i, &cube, true) {
                cube = self.solvers[i - 1].inductive_core();
            } else {
                return (i, cube);
            }
        }
        (self.level() + 1, cube)
    }

    fn generalize(&mut self, mut po: ProofObligation) -> bool {
        let mut mic = self.solvers[po.frame - 1].inductive_core();
        mic = self.mic(po.frame, mic, 0);
        let (frame, mic) = self.push_lemma(po.frame, mic);
        po.frame = frame;
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
            if po.frame == 0 {
                self.add_obligation(po);
                return Some(false);
            }
            assert!(!self.ts.cube_subsume_init(&po.lemma));
            if let Some((bf, _)) = self.frame.trivial_contained(po.frame, &po.lemma) {
                po.frame = bf + 1;
                self.add_obligation(po);
                continue;
            }
            if self.options.verbose > 1 {
                self.frame.statistic();
            }

            self.statistic.qblock_num += 1;
            self.statistic.qblock_avg_cube_len += po.lemma.len();
            let qblock_start = self.statistic.time.start();
            if self.blocked_with_ordered(po.frame, &po.lemma, false, true) {
                self.statistic.qblock_avg_time += self.statistic.time.stop(qblock_start);
                if self.generalize(po) {
                    return None;
                }
            } else {
                self.statistic.qblock_avg_time += self.statistic.time.stop(qblock_start);
                let (model, inputs) = self.get_pred(po.frame);
                self.statistic.avg_po_len += model.len();
                self.add_obligation(ProofObligation::new(
                    po.frame - 1,
                    Lemma::new(model),
                    inputs,
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.add_obligation(po);
            }
        }
        Some(true)
    }

    fn propagate(&mut self) -> bool {
        for frame_idx in self.frame.early..self.level() {
            self.frame[frame_idx].sort_by_key(|x| x.len());
            let frame = self.frame[frame_idx].clone();
            for lemma in frame {
                if self.frame[frame_idx].iter().all(|l| l.ne(&lemma)) {
                    continue;
                }
                self.statistic.qpush_num += 1;
                self.statistic.qpush_avg_cube_len += lemma.len();
                let qpush_start = self.statistic.time.start();
                if self.blocked(frame_idx + 1, &lemma, false) {
                    self.statistic.qpush_avg_time += self.statistic.time.stop(qpush_start);
                    let conflict = self.solvers[frame_idx].inductive_core();
                    self.add_lemma(frame_idx + 1, conflict, true, lemma.po);
                } else {
                    self.statistic.qpush_avg_time += self.statistic.time.stop(qpush_start);
                }
            }
            if self.frame[frame_idx].is_empty() {
                return true;
            }
        }
        self.frame.early = self.level();
        false
    }
}

impl IC3 {
    pub fn new(options: Options, ts: Transys) -> Self {
        let ts = Grc::new(ts);
        let statistic = Statistic::new(&options.model, &ts);
        let activity = Activity::new(&ts);
        let frame = Frames::new(&ts);
        let lift = Lift::new(&ts);
        let mut res = Self {
            options,
            ts,
            activity,
            solvers: Vec::new(),
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
        };
        res.extend();
        res
    }

    fn check(&mut self) -> Option<bool> {
        loop {
            let start = Instant::now();
            loop {
                match self.block() {
                    Some(false) => {
                        self.statistic.overall_block_time += start.elapsed();
                        self.statistic();
                        return Some(false);
                    }
                    None => {
                        self.statistic.overall_block_time += start.elapsed();
                        self.statistic();
                        // self.verify();
                        return Some(true);
                    }
                    _ => (),
                }
                if let Some((bad, inputs)) = self.get_bad() {
                    self.statistic.avg_po_len += bad.len();
                    let bad = Lemma::new(bad);
                    self.add_obligation(ProofObligation::new(self.level(), bad, inputs, 0, None))
                } else {
                    break;
                }
            }
            let blocked_time = start.elapsed();
            if self.options.verbose > 1 {
                self.frame.statistic();
                println!(
                    "[{}:{}] frame: {}, time: {:?}",
                    file!(),
                    line!(),
                    self.level(),
                    blocked_time,
                );
            }
            self.statistic.overall_block_time += blocked_time;
            self.extend();
            let start = Instant::now();
            let propagate = self.propagate();
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
                self.statistic();
                // self.verify();
                return Some(true);
            }
        }
    }

    pub fn check_with_int_hanlder(&mut self) -> bool {
        let ic3 = self as *mut IC3 as usize;
        ctrlc::set_handler(move || {
            let ic3 = unsafe { &mut *(ic3 as *mut IC3) };
            ic3.statistic();
            exit(130);
        })
        .unwrap();
        panic::catch_unwind(AssertUnwindSafe(|| self.check().unwrap())).unwrap_or_else(|_| {
            self.statistic();
            panic!();
        })
    }
}
