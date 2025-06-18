use giputils::statistic::{Average, CountedDuration, RunningTime, SuccessRate};
use std::{fmt::Debug, time::Duration};

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub overall_time: Duration,
    pub get_bad_time: CountedDuration,
    pub blocked_time: CountedDuration,
    pub get_pred_time: Duration,
    pub mic_time: Duration,
    pub push_time: Duration,
}

#[allow(unused)]
#[derive(Debug, Default)]
pub struct Statistic {
    time: RunningTime,

    pub num_mic: usize,
    pub avg_mic_cube_len: Average,
    pub avg_po_cube_len: Average,
    pub mic_drop: SuccessRate,
    pub num_down: usize,
    pub num_down_sat: usize,

    pub ctp: SuccessRate,

    pub block: Block,

    pub overall_propagate_time: Duration,

    pub xor_gen: SuccessRate,
    pub num_auxiliary_var: usize,

    pub test: SuccessRate,
}
