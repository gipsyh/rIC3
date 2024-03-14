use crate::Ic3;
use giputils::statistic::{Average, AverageDuration, Case, RunningTime, SuccessRate};
use std::{fmt::Debug, time::Duration};

#[allow(unused)]
#[derive(Debug, Default)]
pub struct Statistic {
    case: Case,
    pub time: RunningTime,

    pub avg_sat_call_time: AverageDuration,
    pub num_sat_inductive: usize,
    pub sat_inductive_time: Duration,
    pub num_solver_restart: usize,

    pub num_mic: usize,
    pub avg_mic_cube_len: Average,
    pub avg_po_cube_len: Average,
    pub mic_drop: SuccessRate,
    pub num_down: usize,

    pub qgen_num: usize,
    pub qgen_avg_time: AverageDuration,
    pub qgen_avg_cube_len: Average,

    pub qrelind_num: usize,
    pub qrelind_avg_time: AverageDuration,
    pub qrelind_avg_cube_len: Average,

    pub qpush_num: usize,
    pub qpush_avg_time: AverageDuration,
    pub qpush_avg_cube_len: Average,

    pub qtarget_num: usize,
    pub qtarget_avg_time: AverageDuration,

    pub minimal_predecessor_time: Duration,

    pub overall_mic_time: Duration,
    pub overall_block_time: Duration,
    pub overall_propagate_time: Duration,
}

impl Statistic {
    pub fn new(mut case: &str) -> Self {
        if let Some((_, c)) = case.rsplit_once('/') {
            case = c;
        }
        Self {
            case: Case::new(case),
            ..Default::default()
        }
    }
}

impl Ic3 {
    pub fn statistic(&self) {
        self.obligations.statistic();
        self.frames.statistic();
        println!("{:#?}", self.statistic);
    }
}
