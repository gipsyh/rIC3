use logicrs::{DagCnf, Lit, LitFixedVec, LitVec, Var, VarAssign};

#[test]
fn fixed_literals_shrink_in_place() {
    let [a, b, c] = [Var(1).lit(), Var(2).lit(), Var(3).lit()];
    let mut fixed = LitFixedVec::from([a, b, a, a, c, c]);
    let allocation = fixed.as_ptr();
    fixed.dedup();
    assert_eq!(fixed.as_slice(), [a, b, a, c]);
    fixed.retain(|l| *l != b);
    assert_eq!(fixed.as_slice(), [a, a, c]);
    fixed.truncate(2);
    assert_eq!(fixed.as_slice(), [a, a]);
    fixed.truncate(u32::MAX);
    assert_eq!(fixed.len(), 2);
    assert_eq!(fixed.as_ptr(), allocation);
    assert_eq!(fixed.clone().as_slice(), [a, a]);
    fixed.truncate(0);
    assert!(fixed.is_empty());
    assert_eq!(fixed.mem_usage(), 0);
    fixed.dedup();
    fixed.retain(|_| panic!("empty vector must not call predicate"));
    assert_eq!(fixed.as_slice(), []);

    let mut single = LitFixedVec::from([a]);
    single.dedup();
    single.retain(|_| false);
    assert!(single.is_empty());
}

#[test]
fn fixed_literals_remain_valid_when_retain_panics() {
    let mut fixed = LitFixedVec::from([Lit::TRUE, Lit::FALSE, Var(1).lit()]);
    let mut calls = 0;
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        fixed.retain(|_| {
            calls += 1;
            assert!(calls < 3);
            calls == 2
        });
    }));
    assert!(result.is_err());
    // The partially modified contents are still initialized and safe to use.
    assert_eq!(fixed.len(), 3);
    let cloned = fixed.clone();
    assert_eq!(cloned.as_slice(), fixed.as_slice());
    fixed.retain(|_| false);
    assert!(fixed.is_empty());
}

#[test]
fn fixed_literal_simplification_handles_constants_and_complements() {
    let [a, b, c] = [Var(1).lit(), Var(2).lit(), Var(3).lit()];
    let mut values = VarAssign::new_with(Var(3));
    values.set(!a);
    values.set(!c);
    let fixed = LitFixedVec::from([a, a, b, c]);
    let allocation = fixed.as_ptr();
    let simplified = fixed.ordered_simp(&values).unwrap();
    assert_eq!(simplified.as_slice(), [b]);
    assert_eq!(simplified.as_ptr(), allocation);
    assert!(LitFixedVec::from([!a, b]).ordered_simp(&values).is_none());
    assert!(LitFixedVec::from([b, !b]).ordered_simp(&values).is_none());
    assert!(
        LitFixedVec::from([Lit::TRUE])
            .ordered_simp(&values)
            .is_none()
    );
    for fixed in [
        LitFixedVec::new(),
        LitFixedVec::from([a, c]),
        LitFixedVec::from([Lit::FALSE]),
    ] {
        let simplified = fixed.ordered_simp(&values).unwrap();
        assert!(simplified.is_empty());
        assert_eq!(simplified.mem_usage(), 0);
    }
}

#[test]
fn fixed_literal_subsumption_and_resolution() {
    let [a, b, c] = [Var(1).lit(), Var(2).lit(), Var(3).lit()];
    let lhs = LitFixedVec::from([a, c]);
    assert_eq!(
        lhs.ordered_subsume_execpt_one(&LitFixedVec::from([a, b, c])),
        (true, None)
    );
    assert_eq!(
        lhs.ordered_subsume_execpt_one(&LitFixedVec::from([!a, b, c])),
        (false, Some(a))
    );
    assert_eq!(
        lhs.ordered_subsume_execpt_one(&LitFixedVec::from([!a, b, !c])),
        (false, None)
    );
    assert_eq!(
        lhs.ordered_subsume_execpt_one(&LitFixedVec::from([a, b])),
        (false, None)
    );
    let lhs = LitFixedVec::from([a, b]);
    assert_eq!(
        lhs.ordered_resolvent(&LitFixedVec::from([!b, c]), b.var())
            .unwrap()
            .as_slice(),
        [a, c]
    );
    assert!(
        lhs.ordered_resolvent(&LitFixedVec::from([!a, !b]), b.var())
            .is_none()
    );
    assert!(
        LitFixedVec::from([b])
            .ordered_resolvent(&LitFixedVec::from([!b]), b.var())
            .unwrap()
            .is_empty()
    );
}

#[test]
fn fixed_literals_own_their_allocation() {
    assert_eq!(size_of::<LitFixedVec>(), size_of::<usize>());
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<LitFixedVec>();

    for len in [0, 1, 2, 3, 4, 257, 4096] {
        let original: LitVec = (0..len).map(|i| Var::new(i).lit()).collect();
        let mut fixed = LitFixedVec::from(original.clone());
        assert_eq!(fixed.as_slice(), original.as_slice());
        assert_eq!(fixed.mem_usage(), if len == 0 { 0 } else { 4 * (len + 1) });
        let cloned = fixed.clone();
        if len > 0 {
            assert_ne!(fixed.as_ptr(), cloned.as_ptr());
            fixed[0] = !fixed[0];
            fixed.reverse();
        }
        drop(fixed);
        let moved = std::thread::spawn(move || LitVec::from(cloned))
            .join()
            .unwrap();
        assert_eq!(moved, original);
    }
}

fn sample_dag() -> DagCnf {
    let mut dag = DagCnf::new();
    let a = dag.new_var().lit();
    let b = dag.new_var().lit();
    let and = dag.new_and([a, b]);
    dag.new_xor(and, a);
    dag
}

#[test]
fn dag_conversion_preserves_clauses_and_ownership() {
    let dag = sample_dag();
    let expected = dag.lower();
    let pointers: Vec<_> = dag.clause().map(|c| c.as_ptr()).collect();
    let max_var = dag.max_var();
    let mut flat = dag.into_cnf();
    assert_eq!(flat.max_var(), max_var);
    assert_eq!(flat.clauses(), expected.clauses());
    assert_eq!(
        flat.iter().map(|c| c.as_ptr()).collect::<Vec<_>>(),
        pointers
    );
    let clauses = flat.take_clauses();
    assert!(flat.is_empty());
    flat.set_cls(clauses);
    assert_eq!(flat.clauses(), expected.clauses());
}
