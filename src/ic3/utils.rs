use crate::ic3::IC3;
use giputils::statistic::{Average, CountedDuration, RunningTime, SuccessRate};
use logicrs::{Lit, LitVec, SymbolAssign};
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
    pub time: RunningTime,

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

impl IC3 {
    pub(crate) fn lits_symbols(&self, lits: impl IntoIterator<Item = Lit>) -> Vec<SymbolAssign> {
        let lits: LitVec = lits.into_iter().map(|l| self.rst.restore(l)).collect();
        let lits = self.rst.restore_eq_state(&lits);
        let mut symbols = self.symbols.lits_symbols(lits);
        symbols.sort_by(|s1, s2| s1.symbol.cmp(&s2.symbol));
        symbols
    }
}
