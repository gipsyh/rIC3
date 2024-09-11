use giputils::statistic::{Average, Case, RunningTime, SuccessRate};
use std::{fmt::Debug, time::Duration};

#[allow(unused)]
#[derive(Debug, Default)]
pub struct Statistic {
    case: Case,
    time: RunningTime,

    pub num_mic: usize,
    pub avg_mic_cube_len: Average,
    pub avg_po_cube_len: Average,
    pub mic_drop: SuccessRate,
    pub num_down: usize,
    pub num_down_sat: usize,

    pub ctp: SuccessRate,
    pub num_get_bad: usize,

    pub overall_block_time: Duration,
    pub block_get_bad_time: Duration,
    pub block_get_predecessor_time: Duration,
    pub block_blocked_time: Duration,
    pub block_mic_time: Duration,
    pub block_push_time: Duration,
    pub overall_propagate_time: Duration,

    pub xor_gen: SuccessRate,
    pub num_auxiliary_var: usize,

    pub test: SuccessRate,
    pub a: usize,
    pub b: usize,
    pub c: usize,
    pub omic: Duration,
    pub pmic: Duration,
    pub opro: Duration,
    pub ppro: Duration,
    pub ttime: Duration,
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
