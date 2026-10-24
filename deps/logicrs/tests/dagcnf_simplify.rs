use logicrs::{
    DagCnf, Lit, LitVec, Var,
    simplify::{BveObjective, DagCnfSimplify},
};
use std::collections::BTreeSet;

// Existentially quantify unfrozen variables and compare the truth tables over
// the observable variables. BVE may remove internal gate variables entirely.
fn projected_models(dag: &DagCnf, frozen: &[Var]) -> BTreeSet<u32> {
    let mask = frozen.iter().fold(0, |mask, v| {
        if v.is_constant() {
            mask
        } else {
            mask | (1 << (v.0 - 1))
        }
    });
    (0..1 << dag.max_var().0)
        .filter(|bits| {
            dag.clause().all(|clause| {
                clause.iter().any(|l| {
                    // Variable zero denotes false; Lit::TRUE negates it.
                    let value = !l.var().is_constant() && bits & (1 << (l.var().0 - 1)) != 0;
                    value == l.polarity()
                })
            })
        })
        .map(|bits| bits & mask)
        .collect()
}

#[test]
fn simplifying_fixed_clauses_preserves_projected_models() {
    for seed in 0..16 {
        let mut dag = DagCnf::new();
        let a = dag.new_var().lit();
        let b = dag.new_var().lit();
        let c = dag.new_var().lit();
        let and = dag.new_and([a.not_if(seed & 1 != 0), b]);
        let xor = dag.new_xor(and, c.not_if(seed & 2 != 0));
        let or = dag.new_or([and, !xor]);
        let root = dag.new_ite(a, or.not_if(seed & 4 != 0), xor.not_if(seed & 8 != 0));
        for frozen in [
            vec![a.var(), b.var(), c.var(), root.var()],
            dag.var_iter().collect(),
        ] {
            let expected = projected_models(&dag, &frozen);
            assert_eq!(expected.len(), 8);
            let owned = dag.clone().simplify(frozen.iter().copied());
            assert_eq!(
                projected_models(&owned, &frozen),
                expected,
                "owned, seed {seed}"
            );

            let mut borrowed = DagCnfSimplify::new(&dag);
            for &v in &frozen {
                borrowed.froze(v);
            }
            let result = borrowed.simplify();
            assert_eq!(
                projected_models(&result, &frozen),
                expected,
                "borrowed, seed {seed}"
            );
        }
    }
}

#[test]
fn simplifier_deduplicates_and_strengthens_fixed_clauses() {
    let mut dag = DagCnf::new();
    let a = dag.new_var().lit();
    let b = dag.new_var().lit();
    let n = dag.new_var().lit();
    // Resolving the first two clauses strengthens them to [a, n]; the
    // duplicate and subsumed clauses exercise deletion and in-place retain.
    dag.add_rel(
        n.var(),
        &[
            LitVec::from([a, b, b, n]),
            LitVec::from([a, !b, n]),
            LitVec::from([a, b, n]),
        ],
    );
    let frozen: Vec<_> = dag.var_iter().collect();
    let expected = projected_models(&dag, &frozen);
    assert_eq!(expected.len(), 6);
    let mut simplifier = DagCnfSimplify::from_owned(dag);
    for &v in &frozen {
        simplifier.froze(v);
    }
    simplifier.subsume_simplify();
    let result = simplifier.finalize();
    assert_eq!(projected_models(&result, &frozen), expected);
    assert!(result[n.var()].iter().any(|c| c.as_slice() == [a, n]));
}

#[test]
fn simplifier_propagates_constants_with_fixed_clauses() {
    let mut dag = DagCnf::new();
    let a = dag.new_var();
    dag.add_rel(a, &[LitVec::from([a.lit()])]);
    let b = dag.new_var().lit();
    let and = dag.new_and([a.lit(), b]);
    let root = dag.new_and([!a.lit(), and]);
    let frozen: Vec<_> = dag.var_iter().collect();
    let expected = projected_models(&dag, &frozen);
    let simplified = dag.simplify(frozen.iter().copied());
    assert_eq!(projected_models(&simplified, &frozen), expected);
    assert!(
        simplified[root.var()]
            .iter()
            .any(|c| c.as_slice() == [!root])
    );
    assert_eq!(expected.len(), 2);
    assert!(simplified[Var::CONST][0].as_slice() == [Lit::TRUE]);
}

#[test]
fn bve_objectives_choose_differently_when_only_literals_grow() {
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
    let expected = projected_models(&dag, &frozen);
    let before_lits: usize = dag.clause().map(|c| c.len() as usize).sum();
    let before_clauses = dag.num_clause();
    for objective in [BveObjective::Clauses, BveObjective::Literals] {
        let mut simp = DagCnfSimplify::new(&dag);
        for &v in &frozen {
            simp.froze(v);
        }
        // Eliminating the shared AND preserves the clause count, but duplicates
        // its inputs into both outputs and increases the total literal count.
        simp.bve_simplify_with_objective(objective);
        let result = simp.finalize();
        let after_lits: usize = result.clause().map(|c| c.len() as usize).sum();
        assert_eq!(result.num_clause(), before_clauses);
        match objective {
            BveObjective::Clauses => {
                assert!(result[shared.var()].is_empty());
                assert!(after_lits > before_lits);
            }
            BveObjective::Literals => {
                assert!(!result[shared.var()].is_empty());
                assert_eq!(after_lits, before_lits);
            }
        }
        assert_eq!(projected_models(&result, &frozen), expected);
    }
}

#[test]
fn bve_preserves_projected_models_on_generated_gate_networks() {
    use rand::{RngExt, SeedableRng, rngs::StdRng};
    let mut rng = StdRng::seed_from_u64(0xb0e_u64);
    for case in 0..128 {
        let mut dag = DagCnf::new();
        let mut lits: Vec<_> = (0..3).map(|_| dag.new_var().lit()).collect();
        for _ in 0..5 {
            let a = lits[rng.random_range(0..lits.len())].not_if(rng.random());
            let b = lits[rng.random_range(0..lits.len())].not_if(rng.random());
            let c = lits[rng.random_range(0..lits.len())].not_if(rng.random());
            let gate = match rng.random_range(0..4) {
                0 => dag.new_and([a, b, c]),
                1 => dag.new_or([a, b, c]),
                2 => dag.new_xor(a, b),
                _ => dag.new_ite(a, b, c),
            };
            lits.push(gate);
        }
        let frozen: Vec<_> = lits[..3]
            .iter()
            .chain(&lits[6..])
            .map(|l| l.var())
            .collect();
        let expected = projected_models(&dag, &frozen);
        for objective in [BveObjective::Clauses, BveObjective::Literals] {
            let mut simp = DagCnfSimplify::new(&dag);
            for &v in &frozen {
                simp.froze(v);
            }
            simp.const_simplify();
            let before = simp.finalize();
            simp.bve_simplify_with_objective(objective);
            let result = simp.finalize();
            assert_eq!(
                projected_models(&result, &frozen),
                expected,
                "BVE {objective:?} case {case}"
            );
            let cost = |cnf: &DagCnf| match objective {
                BveObjective::Clauses => cnf.num_clause(),
                BveObjective::Literals => cnf.clause().map(|c| c.len() as usize).sum(),
            };
            assert!(
                cost(&result) <= cost(&before),
                "{objective:?} growth in case {case}"
            );
            let result = dag
                .clone()
                .simplify_with_objective(frozen.iter().copied(), objective);
            assert_eq!(
                projected_models(&result, &frozen),
                expected,
                "full {objective:?} case {case}"
            );
        }
    }
}
