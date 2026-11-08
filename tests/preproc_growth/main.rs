#[path = "../it.rs"]
mod it;

use logicrs::DagCnf;
use std::path::Path;

// End-to-end regression for https://github.com/gipsyh/rIC3/issues/211.
// The shared helper enforces a wall-clock timeout, including preprocessing.
#[test]
#[ignore = "slow: run the issue #211 regression manually in release mode"]
fn ic3_model_is_unsat() {
    let model = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/preproc_growth/model.btor");
    it::check(&model, &["ic3"], "UNSAT", false);
}

// https://github.com/gipsyh/rIC3/issues/211
// Small, deterministic reproducer of the clause/literal cost mismatch.
#[test]
fn clause_bounded_bve_can_increase_literals() {
    let mut dag = DagCnf::new();
    let inputs: Vec<_> = (0..5).map(|_| dag.new_var().lit()).collect();
    let shared = dag.new_and(inputs[..3].iter().copied());
    let left = dag.new_or([shared, inputs[3]]);
    let right = dag.new_or([shared, inputs[4]]);
    let frozen: Vec<_> = inputs
        .iter()
        .map(|l| l.var())
        .chain([left.var(), right.var()])
        .collect();
    let before_clauses = dag.num_clause();
    let before_literals: usize = dag.clause().map(|c| c.len() as usize).sum();
    let simplified = dag.simplify(frozen);
    let after_clauses = simplified.num_clause();
    let after_literals: usize = simplified.clause().map(|c| c.len() as usize).sum();
    eprintln!(
        "clauses: {before_clauses} -> {after_clauses}, literals: {before_literals} -> {after_literals}"
    );
    // These assertions describe the current issue, rather than a proposed fix.
    assert!(simplified[shared.var()].is_empty());
    assert!(after_clauses <= before_clauses);
    assert!(after_literals > before_literals);
}
