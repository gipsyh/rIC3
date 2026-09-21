use super::*;
use crate::{
    bmc::{BMC, BMCConfig},
    tracer::{StateTracerIf, state_channel_tracer},
};

/// Two-bit counter from zero; bad when equal to `bad`.
fn counter(bad: usize) -> Transys {
    let mut ts = Transys::new();
    let lo = ts.new_var();
    let hi = ts.new_var();
    let next_hi = ts.rel.new_xor(lo.lit(), hi.lit());
    ts.add_latch(lo, Some(Lit::FALSE), !lo.lit());
    ts.add_latch(hi, Some(Lit::FALSE), next_hi);
    let is_bad = ts.rel.new_and([
        lo.lit().not_if((bad & 1) == 0),
        hi.lit().not_if((bad & 2) == 0),
    ]);
    ts.bad.push(is_bad);
    ts
}

/// Latch stuck at zero, bad when set; the property is inductive.
fn stuck_latch() -> Transys {
    let mut ts = Transys::new();
    let latch = ts.new_var();
    ts.add_latch(latch, Some(Lit::FALSE), latch.lit());
    ts.bad.push(latch.lit());
    ts
}

fn ic3(end: usize, pred_prop: bool, ts: Transys) -> IC3 {
    let mut cfg = IC3Config::default();
    cfg.end = end;
    cfg.pred_prop = pred_prop;
    IC3::new(cfg, ts, VarSymbols::default())
}

/// Runs the engine and returns its result and the traced state events.
fn run(mut engine: impl Engine) -> (McResult, Vec<McResult>) {
    let (tx, rx) = state_channel_tracer();
    engine.add_tracer(Box::new(tx));
    let result = engine.check();
    let events = rx.try_iter().map(|(_, result)| result).collect();
    (result, events)
}

#[test]
fn results_and_traces_match_bmc() {
    for (bad, end) in [(0, 0), (3, 0), (3, 2), (3, 3), (3, usize::MAX)] {
        let mut cfg = BMCConfig::default();
        cfg.end = end;
        let expected = run(BMC::new(cfg, counter(bad)));
        for pred_prop in [false, true] {
            assert_eq!(
                run(ic3(end, pred_prop, counter(bad))),
                expected,
                "bad={bad}, end={end}, pred_prop={pred_prop}"
            );
        }
    }
}

struct TerminateAtDepth(Arc<dyn TerminateCtrl>, usize);

impl TracerIf for TerminateAtDepth {}

#[intertrait::cast_to]
impl StateTracerIf for TerminateAtDepth {
    fn trace_state(&mut self, _: Option<usize>, result: McResult) {
        if result == McResult::Unknown(Some(self.1)) {
            self.0.terminate();
        }
    }
}

#[test]
fn termination_reports_the_last_completed_depth() {
    for pred_prop in [false, true] {
        let mut engine = ic3(usize::MAX, pred_prop, counter(3));
        engine.add_tracer(Box::new(TerminateAtDepth(engine.get_ctrl(), 1)));
        let (result, events) = run(engine);
        assert_eq!(result, McResult::Unknown(Some(1)), "pred_prop={pred_prop}");
        assert_eq!(
            events,
            vec![McResult::Unknown(Some(0)), McResult::Unknown(Some(1))]
        );
    }
}

#[test]
fn bound_does_not_prevent_a_proof() {
    for end in [10, usize::MAX] {
        let (result, events) = run(ic3(end, false, stuck_latch()));
        assert_eq!(result, McResult::UNSAT);
        assert_eq!(events.iter().filter(|&&r| r == McResult::UNSAT).count(), 1);
    }
}
