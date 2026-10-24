use super::op::FolOp;
use super::simplify::SimplifyCtx;
use super::{Sort, Term, Value};
use crate::LboolVec;
use crate::OptLevel;
use giputils::bitvec::BitVec;
use giputils::hash::GHashMap;

fn bv_val(s: &str) -> Value {
    Value::Bv(LboolVec::from(s))
}

fn assert_bv_eq(v: &Value, expected: &str) {
    let bv = v.as_bv().unwrap();
    let expected_bv = LboolVec::from(expected);
    assert_eq!(bv, &expected_bv, "expected {}, got {}", expected, bv);
}

#[test]
fn test_simulate_const() {
    let t = Term::bool_const(true);
    let f = Term::bool_const(false);
    let mut val = GHashMap::new();

    assert_bv_eq(&t.simulate(&mut val), "1");
    assert_bv_eq(&f.simulate(&mut val), "0");
}

#[test]
fn test_simulate_var_default() {
    // Variable not in val should default to X
    let x = Term::new_var(Sort::Bv(4));
    let mut val = GHashMap::new();

    assert_bv_eq(&x.simulate(&mut val), "xxxx");
}

#[test]
fn test_simulate_var_with_value() {
    let x = Term::new_var(Sort::Bv(4));
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1010"));

    assert_bv_eq(&x.simulate(&mut val), "1010");
}

#[test]
fn test_simulate_not() {
    let x = Term::new_var(Sort::Bv(4));
    let not_x = !&x;

    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1010"));

    assert_bv_eq(&not_x.simulate(&mut val), "0101");
}

#[test]
fn test_simulate_and_or_xor() {
    let x = Term::new_var(Sort::Bv(4));
    let y = Term::new_var(Sort::Bv(4));

    let and_xy = &x & &y;
    let or_xy = &x | &y;
    let xor_xy = &x ^ &y;

    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1100"));
    val.insert(y.clone(), bv_val("1010"));

    assert_bv_eq(&and_xy.simulate(&mut val), "1000");
    assert_bv_eq(&or_xy.simulate(&mut val), "1110");
    assert_bv_eq(&xor_xy.simulate(&mut val), "0110");
}

#[test]
fn test_simulate_ite() {
    let c = Term::new_var(Sort::Bv(1));
    let t = Term::new_var(Sort::Bv(4));
    let e = Term::new_var(Sort::Bv(4));

    let ite = c.ite(&t, &e);

    // Test when condition is true
    let mut val = GHashMap::new();
    val.insert(c.clone(), bv_val("1"));
    val.insert(t.clone(), bv_val("1111"));
    val.insert(e.clone(), bv_val("0000"));
    assert_bv_eq(&ite.simulate(&mut val), "1111");
}

#[test]
fn test_simulate_nested_expr() {
    // Test: (x & y) | (!x & z)
    let x = Term::new_var(Sort::Bv(4));
    let y = Term::new_var(Sort::Bv(4));
    let z = Term::new_var(Sort::Bv(4));

    let expr = (&x & &y) | (!&x & &z);

    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1100"));
    val.insert(y.clone(), bv_val("1010"));
    val.insert(z.clone(), bv_val("0101"));

    // x & y = 1000
    // !x = 0011
    // !x & z = 0001
    // result = 1001
    assert_bv_eq(&expr.simulate(&mut val), "1001");
}

#[test]
fn test_simulate_with_unknown() {
    let x = Term::new_var(Sort::Bv(4));
    let y = Term::new_var(Sort::Bv(4));

    let and_xy = &x & &y;

    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1x00"));
    val.insert(y.clone(), bv_val("1100"));

    // 1x00 & 1100 = 1x00 (x & 1 = x, x & 0 = 0)
    assert_bv_eq(&and_xy.simulate(&mut val), "1x00");
}

#[test]
fn test_simplify_and_or_identities() {
    let x = Term::new_var(Sort::Bv(1));

    let and_expr = Term::bool_const(true) & &x;
    let mut map = GHashMap::new();
    assert_eq!(and_expr.simplify(&mut map), x);

    let or_expr = Term::bool_const(false) | &x;
    let mut map = GHashMap::new();
    assert_eq!(or_expr.simplify(&mut map), x);

    // Commutative fallback: ordered rule expects constants on the left.
    let and_expr = &x & Term::bool_const(true);
    let mut map = GHashMap::new();
    assert_eq!(and_expr.simplify(&mut map), x);

    let or_expr = &x | Term::bool_const(false);
    let mut map = GHashMap::new();
    assert_eq!(or_expr.simplify(&mut map), x);
}

#[test]
fn test_simplify_xor_identities() {
    let x = Term::new_var(Sort::Bv(1));

    let xor0 = Term::bool_const(false) ^ &x;
    let mut map = GHashMap::new();
    assert_eq!(xor0.simplify(&mut map), x);

    let xor1 = Term::bool_const(true) ^ &x;
    let mut map = GHashMap::new();
    assert_eq!(xor1.simplify(&mut map), !x.clone());

    // Commutative fallback
    let xor0 = &x ^ Term::bool_const(false);
    let mut map = GHashMap::new();
    assert_eq!(xor0.simplify(&mut map), x);
}

#[test]
fn test_simplify_associative_constants() {
    let x = Term::new_var(Sort::Bv(4));
    let c3 = Term::bv_const(BitVec::from("0011"));
    let c5 = Term::bv_const(BitVec::from("0101"));
    let c6 = Term::bv_const(BitVec::from("0110"));
    let c8 = Term::bv_const(BitVec::from("1000"));

    let mut map = GHashMap::new();
    assert_eq!(((&x + &c3) + &c5).simplify(&mut map), &x + &c8);

    let mut map = GHashMap::new();
    assert_eq!(((&x ^ &c3) ^ &c5).simplify(&mut map), &x ^ &c6);

    let mut map = GHashMap::new();
    assert_eq!(
        ((&x & &c3) & &c5).simplify(&mut map),
        &x & &Term::bv_const(BitVec::from("0001"))
    );
}

#[test]
fn test_simplify_not_not() {
    let x = Term::new_var(Sort::Bv(1));
    let expr = !!&x;
    let mut map = GHashMap::new();
    assert_eq!(expr.simplify(&mut map), x);
}

#[test]
fn test_simplify_ite_same_nested_condition() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let z = Term::new_var(Sort::Bv(8));

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(c.ite(&x, &y), &z).simplify_with_ctx(&ctx, &mut map),
        c.ite(&x, &z)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&x, c.ite(&y, &z)).simplify_with_ctx(&ctx, &mut map),
        c.ite(&x, &z)
    );
}

#[test]
fn test_simplify_ite_not_branches() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(!&x, !&y).simplify_with_ctx(&ctx, &mut map),
        !c.ite(&x, &y)
    );
}

#[test]
fn test_simplify_ite_nested_shared_branch() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let d = Term::new_var(Sort::bool());
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(d.ite(&x, &y), &y).simplify_with_ctx(&ctx, &mut map),
        (&c & &d).ite(&x, &y)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(d.ite(&y, &x), &y).simplify_with_ctx(&ctx, &mut map),
        (&c & !&d).ite(&x, &y)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&x, d.ite(&x, &y)).simplify_with_ctx(&ctx, &mut map),
        (&c | &d).ite(&x, &y)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&x, d.ite(&y, &x)).simplify_with_ctx(&ctx, &mut map),
        (&c | !&d).ite(&x, &y)
    );
}

fn signed_min(width: usize) -> Term {
    let mut c = BitVec::zero(width);
    c.set(width - 1, true);
    Term::bv_const(c)
}

fn signed_max(width: usize) -> Term {
    let mut c = BitVec::ones(width);
    c.set(width - 1, false);
    Term::bv_const(c)
}

#[test]
fn test_simplify_slt_identities() {
    let x = Term::new_var(Sort::Bv(8));
    let mut map = GHashMap::new();
    assert_eq!(
        x.op1(super::op::FolOp::Slt, &x).simplify(&mut map),
        Term::bool_const(false)
    );
}

#[test]
fn test_simplify_slt_signed_extremes() {
    let x = Term::new_var(Sort::Bv(8));
    let min = signed_min(8);
    let max = signed_max(8);

    let mut map = GHashMap::new();
    assert_eq!(
        min.op1(super::op::FolOp::Slt, &x).simplify(&mut map),
        !min.op1(super::op::FolOp::Eq, &x)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        max.op1(super::op::FolOp::Slt, &x).simplify(&mut map),
        Term::bool_const(false)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        x.op1(super::op::FolOp::Slt, &min).simplify(&mut map),
        Term::bool_const(false)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        x.op1(super::op::FolOp::Slt, &max).simplify(&mut map),
        !x.op1(super::op::FolOp::Eq, &max)
    );
}

#[test]
fn test_simplify_slice_of_concat() {
    let hi = Term::new_var(Sort::Bv(4));
    let lo = Term::new_var(Sort::Bv(8));
    let concat = hi.concat(&lo);

    let mut map = GHashMap::new();
    assert_eq!(concat.slice(1, 3).simplify(&mut map), lo.slice(1, 3));

    let mut map = GHashMap::new();
    assert_eq!(concat.slice(8, 10).simplify(&mut map), hi.slice(0, 2));

    let mut map = GHashMap::new();
    let expected = hi.slice(0, 1).concat(lo.slice(6, 7));
    assert_eq!(concat.slice(6, 9).simplify(&mut map), expected);
}

#[test]
fn test_simplify_slice_pushdown_patterns() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&x, &y).slice(2, 4).simplify_with_ctx(&ctx, &mut map),
        c.ite(x.slice(2, 4), y.slice(2, 4))
    );

    let mut map = GHashMap::new();
    assert_eq!(
        (&x & &y).slice(2, 4).simplify_with_ctx(&ctx, &mut map),
        x.slice(2, 4) & y.slice(2, 4)
    );

    let ext = Term::new_op(FolOp::Sext, [&x, &Term::bv_const(BitVec::zero(4))]);
    let mut map = GHashMap::new();
    assert_eq!(
        ext.slice(1, 3).simplify_with_ctx(&ctx, &mut map),
        x.slice(1, 3)
    );
}

#[test]
fn test_simplify_low_bit_arith_shift_patterns() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));

    let mut map = GHashMap::new();
    assert_eq!(
        (&x + &y).slice(0, 0).simplify_with_ctx(&ctx, &mut map),
        x.slice(0, 0) ^ y.slice(0, 0)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        (&x - &y).slice(0, 0).simplify_with_ctx(&ctx, &mut map),
        x.slice(0, 0) ^ y.slice(0, 0)
    );

    let mut map = GHashMap::new();
    let sll = x.op1(FolOp::Sll, &y);
    assert_eq!(
        sll.slice(0, 0).simplify_with_ctx(&ctx, &mut map),
        y.op1(FolOp::Eq, y.mk_bv_const_zero()) & x.slice(0, 0)
    );
}

#[test]
fn test_simplify_slice_of_neg() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let x = Term::new_var(Sort::Bv(8));
    let neg_x = x.op0(FolOp::Neg);

    // slice starting at the lsb may be pushed through the negation
    let mut map = GHashMap::new();
    assert_eq!(
        neg_x.slice(0, 3).simplify_with_ctx(&ctx, &mut map),
        x.slice(0, 3).op0(FolOp::Neg)
    );

    // but not a slice starting above the lsb: bit l of neg(x) depends on x[0..l)
    let mut map = GHashMap::new();
    assert_eq!(
        neg_x.slice(1, 1).simplify_with_ctx(&ctx, &mut map),
        neg_x.slice(1, 1)
    );
    let mut map = GHashMap::new();
    assert_eq!(
        neg_x.slice(2, 5).simplify_with_ctx(&ctx, &mut map),
        neg_x.slice(2, 5)
    );
}

#[test]
fn test_simplify_slice_of_neg_preserves_semantics() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let w = 4;
    let x = Term::new_var(Sort::Bv(w));
    let neg_x = x.op0(FolOp::Neg);
    for l in 0..w {
        for h in l..w {
            let orig = neg_x.slice(l, h);
            let mut map = GHashMap::new();
            let simp = orig.simplify_with_ctx(&ctx, &mut map);
            for v in 0..(1usize << w) {
                let bits: String = (0..w)
                    .rev()
                    .map(|i| if (v >> i) & 1 == 1 { '1' } else { '0' })
                    .collect();
                let mut val = GHashMap::new();
                val.insert(x.clone(), bv_val(&bits));
                let expected = orig.simulate(&mut val);
                let mut val = GHashMap::new();
                val.insert(x.clone(), bv_val(&bits));
                let got = simp.simulate(&mut val);
                assert_eq!(
                    got.as_bv().unwrap(),
                    expected.as_bv().unwrap(),
                    "slice(neg(x), {l}, {h}) with x = {bits}: expected {}, got {}",
                    expected.as_bv().unwrap(),
                    got.as_bv().unwrap()
                );
            }
        }
    }
}

#[test]
fn test_simplify_nonnegative_slt_bound() {
    let x = Term::new_var(Sort::Bv(6));
    let zx = Term::bv_const(BitVec::zero(2)).concat(&x);
    let bound = Term::bv_const(BitVec::from("01000000"));
    let mut map = GHashMap::new();
    assert_eq!(
        zx.op1(FolOp::Slt, &bound).simplify(&mut map),
        Term::bool_const(true)
    );
}

#[test]
fn test_simplify_ult_zero_extended_lhs_const_bound() {
    let ctx = SimplifyCtx::new(OptLevel::O1);
    let x = Term::new_var(Sort::Bv(2));
    let zx = Term::bv_const(BitVec::zero(4)).concat(&x);
    let bound = Term::bv_const(BitVec::from("100000"));

    let mut map = GHashMap::new();
    assert_eq!(
        zx.op1(FolOp::Ult, &bound).simplify_with_ctx(&ctx, &mut map),
        Term::bool_const(true)
    );
}

#[test]
fn test_simplify_ult_const_zero_extended_rhs_bound() {
    let ctx = SimplifyCtx::new(OptLevel::O1);
    let y = Term::new_var(Sort::Bv(2));
    let zy = Term::bv_const(BitVec::zero(4)).concat(&y);
    let lhs = Term::bv_const(BitVec::from("100000"));

    let mut map = GHashMap::new();
    assert_eq!(
        lhs.op1(FolOp::Ult, &zy).simplify_with_ctx(&ctx, &mut map),
        Term::bool_const(false)
    );
}

#[test]
fn test_simplify_bool_mask_patterns() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let x = Term::new_var(Sort::Bv(8));
    let mask = c.ite(x.mk_bv_const_ones(), x.mk_bv_const_zero());

    let mut map = GHashMap::new();
    assert_eq!(
        (&x & &mask).simplify_with_ctx(&ctx, &mut map),
        c.ite(&x, x.mk_bv_const_zero())
    );

    let mut map = GHashMap::new();
    assert_eq!(
        (&x & !&mask).simplify_with_ctx(&ctx, &mut map),
        c.ite(x.mk_bv_const_zero(), &x)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        (mask.op1(FolOp::Eq, x.mk_bv_const_zero())).simplify_with_ctx(&ctx, &mut map),
        !&c
    );

    let y = Term::new_var(Sort::Bv(8));
    let mut map = GHashMap::new();
    let masked_mux = ((&x & !&mask) | (&y & &mask)).simplify_with_ctx(&ctx, &mut map);
    assert_eq!(masked_mux, c.ite(&y, &x));

    let sext_mask = Term::new_op(FolOp::Sext, [&c, &Term::bv_const(BitVec::zero(7))]);
    let mut map = GHashMap::new();
    assert_eq!(
        (&x & &sext_mask).simplify_with_ctx(&ctx, &mut map),
        c.ite(&x, x.mk_bv_const_zero())
    );

    let mut map = GHashMap::new();
    assert_eq!(
        sext_mask
            .op1(FolOp::Eq, sext_mask.mk_bv_const_zero())
            .simplify_with_ctx(&ctx, &mut map),
        !&c
    );
}

#[test]
fn test_simplify_array_same_index_patterns() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let array = Term::new_var(Sort::Array(3, 8));
    let index = Term::new_var(Sort::Bv(3));
    let value = Term::new_var(Sort::Bv(8));
    let read = Term::new_op(FolOp::Read, [&array, &index]);
    let write = Term::new_op(FolOp::Write, [&array, &index, &value]);

    let mut map = GHashMap::new();
    assert_eq!(
        Term::new_op(FolOp::Read, [&write, &index]).simplify_with_ctx(&ctx, &mut map),
        value
    );

    let mut map = GHashMap::new();
    assert_eq!(
        Term::new_op(FolOp::Write, [&array, &index, &read]).simplify_with_ctx(&ctx, &mut map),
        array
    );

    let conditional_value = c.ite(&value, &read);
    let conditional_write = Term::new_op(FolOp::Write, [&array, &index, &conditional_value]);
    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&conditional_write, &array)
            .simplify_with_ctx(&ctx, &mut map),
        c.ite(Term::new_op(FolOp::Write, [&array, &index, &value]), &array)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        Term::new_op(FolOp::Write, [&array, &index, &c.ite(&value, &read)])
            .simplify_with_ctx(&ctx, &mut map),
        c.ite(Term::new_op(FolOp::Write, [&array, &index, &value]), &array)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        Term::new_op(FolOp::Write, [&array, &index, &c.ite(&read, &value)])
            .simplify_with_ctx(&ctx, &mut map),
        c.ite(&array, Term::new_op(FolOp::Write, [&array, &index, &value]))
    );
}

// Regression tests for the Ult/Slt sort bug.
//
// Before the fix, FolOp::sort() returned terms[0].sort() (the operand width)
// for Ult and Slt instead of Sort::Bv(1).  The BTOR2 parser asserts that the
// sort computed by new_op matches the sort declared in the BTOR2 file; for any
// N-bit (N > 1) comparison this assertion would fire immediately on parse.
//
// Minimal reproducer BTOR2:
//   1 sort bitvec 1
//   2 sort bitvec 8
//   3 input 2 a
//   4 input 2 b
//   5 ult 1 3 4    ← panicked here before the fix
//   6 bad 5

#[test]
fn test_ult_result_sort_is_one_bit() {
    // Operands are 8-bit; result must be 1-bit regardless.
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let ult = x.op1(super::op::FolOp::Ult, &y);
    assert_eq!(
        ult.sort(),
        Sort::Bv(1),
        "ult of 8-bit operands must have sort bitvec 1"
    );
}

#[test]
fn test_slt_result_sort_is_one_bit() {
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let slt = x.op1(super::op::FolOp::Slt, &y);
    assert_eq!(
        slt.sort(),
        Sort::Bv(1),
        "slt of 8-bit operands must have sort bitvec 1"
    );
}

#[test]
fn test_ult_simulate() {
    // Strings are MSB-first; LboolVec::from reverses them to LSB-first internally.
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let ult = x.op1(super::op::FolOp::Ult, &y);

    // 5 < 10 → true
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00000101")); // 5
    val.insert(y.clone(), bv_val("00001010")); // 10
    assert_bv_eq(&ult.simulate(&mut val), "1");

    // 10 < 5 → false
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00001010")); // 10
    val.insert(y.clone(), bv_val("00000101")); // 5
    assert_bv_eq(&ult.simulate(&mut val), "0");

    // 5 < 5 → false (equal, not strictly less)
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00000101")); // 5
    val.insert(y.clone(), bv_val("00000101")); // 5
    assert_bv_eq(&ult.simulate(&mut val), "0");
}

#[test]
fn test_slt_simulate() {
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let slt = x.op1(super::op::FolOp::Slt, &y);

    // -1 (0xFF) < 1 (0x01) → true (signed)
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("11111111")); // -1
    val.insert(y.clone(), bv_val("00000001")); //  1
    assert_bv_eq(&slt.simulate(&mut val), "1");

    // 1 < -1 → false (signed)
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00000001")); //  1
    val.insert(y.clone(), bv_val("11111111")); // -1
    assert_bv_eq(&slt.simulate(&mut val), "0");

    // 5 < 10 → true (positive values, same as unsigned)
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00000101")); // 5
    val.insert(y.clone(), bv_val("00001010")); // 10
    assert_bv_eq(&slt.simulate(&mut val), "1");
}

#[test]
fn test_simplify_eq_and_const_contradiction() {
    let ctx = SimplifyCtx::new(OptLevel::O1);
    let x = Term::new_var(Sort::Bv(7));

    // Eq(And(x, 1110111), 1100111) -> satisfiable, not simplified to false
    let c1 = Term::bv_const(BitVec::from("1110111"));
    let c2 = Term::bv_const(BitVec::from("1100111"));
    let eq_satisfiable = (&x & &c1).op1(FolOp::Eq, &c2);
    let mut map = GHashMap::new();
    assert_ne!(
        eq_satisfiable.simplify_with_ctx(&ctx, &mut map),
        Term::bool_const(false)
    );

    // Eq(And(x, 1110111), 1111111) -> contradiction (bit 3 of mask is 0, but bit 3 of target is 1)
    let c3 = Term::bv_const(BitVec::from("1111111"));
    let eq_contradiction = (&x & &c1).op1(FolOp::Eq, &c3);
    let mut map = GHashMap::new();
    assert_eq!(
        eq_contradiction.simplify_with_ctx(&ctx, &mut map),
        Term::bool_const(false)
    );
}

/// Agreement of the simulator, the bit-blaster and an independent reference for the shift,
/// rotate and division operators on constant operands, including the widths where a `usize` /
/// `u128` intermediate used to overflow (64, 128) and division by zero.
mod const_arith {
    use super::*;
    use crate::fol::TermVec;
    use FolOp::*;
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    const OPS: [FolOp; 10] = [Sll, Srl, Sra, Rol, Ror, Udiv, Urem, Sdiv, Srem, Smod];

    fn bv_from_fn(w: usize, f: impl FnMut(usize) -> bool) -> BitVec {
        (0..w).map(f).collect()
    }

    fn bv_from_u128(w: usize, v: u128) -> BitVec {
        bv_from_fn(w, |i| i < 128 && (v >> i) & 1 == 1)
    }

    fn bv_to_u128(x: &BitVec) -> u128 {
        assert!(x.len() <= 128);
        x.iter()
            .enumerate()
            .fold(0, |acc, (i, b)| acc | ((b as u128) << i))
    }

    fn bv_to_i128(x: &BitVec) -> i128 {
        let w = x.len();
        let v = bv_to_u128(x);
        if w < 128 && x.sign_bit() {
            (v | (u128::MAX << w)) as i128
        } else {
            v as i128
        }
    }

    fn ref_neg(x: &BitVec) -> BitVec {
        let mut res = BitVec::zero(x.len());
        let mut carry = true;
        for i in 0..x.len() {
            let b = !x.get(i);
            res.set(i, b ^ carry);
            carry &= b;
        }
        res
    }

    fn ref_abs(x: &BitVec) -> (BitVec, bool) {
        if x.sign_bit() {
            (ref_neg(x), true)
        } else {
            (x.clone(), false)
        }
    }

    fn ref_ult(x: &BitVec, y: &BitVec) -> bool {
        for i in (0..x.len()).rev() {
            if x.get(i) != y.get(i) {
                return y.get(i);
            }
        }
        false
    }

    /// Native reference for widths <= 128 (SMT-LIB semantics, division by zero included).
    fn reference_native(op: FolOp, x: &BitVec, y: &BitVec) -> BitVec {
        let w = x.len();
        let (xu, yu) = (bv_to_u128(x), bv_to_u128(y));
        let (xs, ys) = (bv_to_i128(x), bv_to_i128(y));
        let mask = bv_to_u128(&BitVec::ones(w));
        let ones = bv_from_u128(w, mask);
        let shl = |v: u128, s: u128| if s >= w as u128 { 0 } else { v << s };
        let shr = |v: u128, s: u128| if s >= w as u128 { 0 } else { v >> s };
        let rot = yu % w as u128;
        match op {
            Sll => bv_from_u128(w, shl(xu, yu)),
            Srl => bv_from_u128(w, shr(xu, yu)),
            Sra => {
                let fill = if x.sign_bit() {
                    mask & !shr(mask, yu)
                } else {
                    0
                };
                bv_from_u128(w, shr(xu, yu) | fill)
            }
            Rol => bv_from_u128(w, shl(xu, rot) | shr(xu, (w as u128 - rot) % w as u128)),
            Ror => bv_from_u128(w, shr(xu, rot) | shl(xu, (w as u128 - rot) % w as u128)),
            Udiv if yu == 0 => ones,
            Udiv => bv_from_u128(w, xu / yu),
            Urem if yu == 0 => x.clone(),
            Urem => bv_from_u128(w, xu % yu),
            Sdiv if ys == 0 => {
                if xs < 0 {
                    bv_from_u128(w, 1)
                } else {
                    ones
                }
            }
            Sdiv => bv_from_u128(w, xs.wrapping_div(ys) as u128),
            Srem if ys == 0 => x.clone(),
            Srem => bv_from_u128(w, xs.wrapping_rem(ys) as u128),
            Smod if ys == 0 => x.clone(),
            Smod => {
                let r = xs.wrapping_rem(ys);
                let r = if r != 0 && (r < 0) != (ys < 0) {
                    r.wrapping_add(ys)
                } else {
                    r
                };
                bv_from_u128(w, r as u128)
            }
            _ => unreachable!(),
        }
    }

    /// Reference for the shift and rotate operators at any width, by moving bits.
    fn reference_shift(op: FolOp, x: &BitVec, y: &BitVec) -> BitVec {
        let w = x.len();
        // shift amount saturated at w; a set bit at index >= 64 is always >= w
        let shift = y
            .iter()
            .enumerate()
            .filter(|(_, b)| *b)
            .map(|(i, _)| if i >= 64 { w } else { (1usize << i).min(w) })
            .fold(0usize, |acc, v| (acc + v).min(w));
        // rotation amount modulo w: bit i contributes 2^i mod w
        let mut pow = 1 % w;
        let mut rot = 0;
        for b in y.iter() {
            if b {
                rot = (rot + pow) % w;
            }
            pow = (pow * 2) % w;
        }
        match op {
            Sll => bv_from_fn(w, |i| i >= shift && x.get(i - shift)),
            Srl => bv_from_fn(w, |i| i + shift < w && x.get(i + shift)),
            Sra => bv_from_fn(w, |i| {
                if i + shift < w {
                    x.get(i + shift)
                } else {
                    x.sign_bit()
                }
            }),
            Rol => bv_from_fn(w, |i| x.get((i + w - rot) % w)),
            Ror => bv_from_fn(w, |i| x.get((i + rot) % w)),
            _ => unreachable!(),
        }
    }

    fn words(x: &BitVec) -> Vec<u64> {
        let mut w = vec![0u64; x.len().div_ceil(64)];
        for (i, b) in x.iter().enumerate() {
            w[i / 64] |= (b as u64) << (i % 64);
        }
        w
    }

    /// `q * y + r` on 64-bit limbs without truncation (2n + 1 words).
    fn ref_mul_add(q: &BitVec, y: &BitVec, r: &BitVec) -> Vec<u64> {
        let (q, y, r) = (words(q), words(y), words(r));
        let n = q.len();
        let mut acc = vec![0u64; 2 * n + 1];
        let add_at = |acc: &mut Vec<u64>, mut k: usize, mut v: u128| {
            while v != 0 {
                let t = acc[k] as u128 + v;
                acc[k] = t as u64;
                v = t >> 64;
                k += 1;
            }
        };
        for (i, &qi) in q.iter().enumerate() {
            for (j, &yj) in y.iter().enumerate() {
                add_at(&mut acc, i + j, qi as u128 * yj as u128);
            }
        }
        for (k, &rk) in r.iter().enumerate() {
            add_at(&mut acc, k, rk as u128);
        }
        acc
    }

    /// Oracle for unsigned division at any width: `x = q * y + r` without truncation and
    /// `r < y`, or `(q, r) = (ones, x)` for `y = 0`. Euclidean division is unique, so this is a
    /// complete check.
    fn assert_udivrem(x: &BitVec, y: &BitVec, q: &BitVec, r: &BitVec) {
        if y.is_zero() {
            assert!(
                q.is_ones() && r == x,
                "udiv/urem by zero: x={x:b} q={q:b} r={r:b}"
            );
            return;
        }
        assert!(
            ref_ult(r, y),
            "remainder not below divisor: x={x:b} y={y:b} r={r:b}"
        );
        let mut xw = words(x);
        xw.resize(2 * xw.len() + 1, 0);
        assert_eq!(
            ref_mul_add(q, y, r),
            xw,
            "q * y + r != x: x={x:b} y={y:b} q={q:b} r={r:b}"
        );
    }

    /// Reference for the division operators at any width: the unsigned quotient and remainder of
    /// the magnitudes are taken from the simulator and checked with `assert_udivrem`; the signed
    /// results follow the SMT-LIB definitions of bvsdiv, bvsrem and bvsmod.
    fn reference_div(op: FolOp, x: &BitVec, y: &BitVec) -> BitVec {
        let signed = matches!(op, Sdiv | Srem | Smod);
        let (ax, nx) = if signed {
            ref_abs(x)
        } else {
            (x.clone(), false)
        };
        let (ay, ny) = if signed {
            ref_abs(y)
        } else {
            (y.clone(), false)
        };
        let sim = |op: FolOp, a: &BitVec, b: &BitVec| {
            let v = op.simulate(&[Value::Bv(a.clone().into()), Value::Bv(b.clone().into())]);
            BitVec::from(v.into_bv().unwrap())
        };
        let (q, r) = (sim(Udiv, &ax, &ay), sim(Urem, &ax, &ay));
        assert_udivrem(&ax, &ay, &q, &r);
        let add = |a: &BitVec, b: &BitVec| sim(Add, a, b);
        match op {
            Udiv => q,
            Urem => r,
            Sdiv if nx != ny => ref_neg(&q),
            Sdiv => q,
            Srem if nx => ref_neg(&r),
            Srem => r,
            Smod if r.is_zero() => r,
            Smod => match (nx, ny) {
                (false, false) => r,
                (true, false) => add(&ref_neg(&r), y),
                (false, true) => add(&r, y),
                (true, true) => ref_neg(&r),
            },
            _ => unreachable!(),
        }
    }

    fn reference(op: FolOp, x: &BitVec, y: &BitVec) -> BitVec {
        let generic = match op {
            Sll | Srl | Sra | Rol | Ror => reference_shift(op, x, y),
            _ => reference_div(op, x, y),
        };
        if x.len() <= 128 {
            assert_eq!(
                generic,
                reference_native(op, x, y),
                "{op:?} references disagree: x={x:b} y={y:b}"
            );
        }
        generic
    }

    fn simulate(op: FolOp, x: &BitVec, y: &BitVec) -> BitVec {
        let v = op.simulate(&[Value::Bv(x.clone().into()), Value::Bv(y.clone().into())]);
        let v = v.into_bv().unwrap();
        assert!(
            !v.any_x(),
            "{op:?} simulated X on constants: x={x:b} y={y:b} -> {v}"
        );
        v.into()
    }

    /// Bit-blast on constant bits; every gate folds, so the result is a constant.
    fn bitblast_const(op: FolOp, x: &BitVec, y: &BitVec) -> BitVec {
        let xb: TermVec = x.iter().map(Term::bool_const).collect();
        let yb: TermVec = y.iter().map(Term::bool_const).collect();
        op.bitblast(&[xb, yb])
            .iter()
            .map(|t| {
                t.try_bv_const()
                    .expect("bitblast of constants did not fold")
                    .get(0)
            })
            .collect()
    }

    /// Bit-blasted circuit over variable operands, evaluated by simulation of the boolean terms.
    struct Circuit {
        x: TermVec,
        y: TermVec,
        out: TermVec,
    }

    impl Circuit {
        fn new(op: FolOp, w: usize) -> Self {
            let x = Term::new_var(Sort::Bv(w));
            let y = Term::new_var(Sort::Bv(w));
            let t = Term::new_op(op, [&x, &y]);
            let mut map = GHashMap::new();
            let out = t.bitblast(&mut map);
            Self {
                x: x.bitblast(&mut map),
                y: y.bitblast(&mut map),
                out,
            }
        }

        fn eval(&self, x: &BitVec, y: &BitVec) -> BitVec {
            let mut val = GHashMap::new();
            for (t, b) in self
                .x
                .iter()
                .zip(x.iter())
                .chain(self.y.iter().zip(y.iter()))
            {
                val.insert(t.clone(), Value::Bv(BitVec::from(&[b]).into()));
            }
            self.out
                .iter()
                .map(|t| {
                    let v = t.simulate(&mut val);
                    let v = v.as_bv().unwrap();
                    assert!(!v.any_x());
                    v.get(0).is_true()
                })
                .collect()
        }
    }

    /// `Term::new_op` on two constants must fold to the reference constant, and the fold must be
    /// stable under `simplify_with_ctx` at O3.
    fn assert_simplify_folds(op: FolOp, x: &BitVec, y: &BitVec, expected: &BitVec) {
        let t = Term::new_op(op, [Term::bv_const(x.clone()), Term::bv_const(y.clone())]);
        assert_eq!(
            t.try_bv_const(),
            Some(expected),
            "{op:?} fold: x={x:b} y={y:b}"
        );
        let ctx = SimplifyCtx::new(OptLevel::O3);
        let mut map = GHashMap::new();
        assert_eq!(
            t.simplify_with_ctx(&ctx, &mut map),
            Term::bv_const(expected.clone())
        );
    }

    fn check(op: FolOp, x: &BitVec, y: &BitVec, blast: bool, circuit: Option<&Circuit>) {
        let expected = reference(op, x, y);
        assert_eq!(
            simulate(op, x, y),
            expected,
            "{op:?} simulate: x={x:b} y={y:b}"
        );
        assert_simplify_folds(op, x, y, &expected);
        if blast {
            let got = match circuit {
                Some(c) => c.eval(x, y),
                None => bitblast_const(op, x, y),
            };
            assert_eq!(got, expected, "{op:?} bitblast: x={x:b} y={y:b}");
        }
    }

    #[test]
    fn exhaustive_small_widths() {
        for w in 1..=5 {
            for op in OPS {
                let circuit = Circuit::new(op, w);
                for xv in 0..(1u128 << w) {
                    for yv in 0..(1u128 << w) {
                        check(
                            op,
                            &bv_from_u128(w, xv),
                            &bv_from_u128(w, yv),
                            true,
                            Some(&circuit),
                        );
                    }
                }
            }
        }
    }

    fn random_bv(rng: &mut StdRng, w: usize) -> BitVec {
        bv_from_fn(w, |_| rng.random::<bool>())
    }

    /// Boundary patterns: zero, one, all ones, signed min and max, and a single set bit at the
    /// indices where a `usize`, `u128` or `i128` intermediate overflows.
    fn patterns(w: usize) -> Vec<BitVec> {
        let mut v = vec![
            BitVec::zero(w),
            BitVec::one(w),
            BitVec::ones(w),
            bv_from_fn(w, |i| i == w - 1),
            bv_from_fn(w, |i| i != w - 1),
        ];
        for k in [63, 64, 127, 128] {
            if k < w - 1 {
                v.push(bv_from_fn(w, |i| i == k));
            }
        }
        v
    }

    /// Every operand pair goes through simulate, reference and the constant fold. The bit-blast
    /// cross-check runs with the last (random) operand as `x` for the shifts and rotations, and
    /// on a single point for the dividers, whose bit-blast costs about a second at width 200 in
    /// a debug build.
    #[test]
    fn random_wide_widths() {
        let mut rng = StdRng::seed_from_u64(0x5eed);
        for w in [63, 64, 65, 70, 100, 127, 128, 129, 140, 200] {
            let mut vals = patterns(w);
            vals.extend((0..2).map(|_| random_bv(&mut rng, w)));
            let last = vals.len() - 1;
            for op in OPS {
                let shift = matches!(op, Sll | Srl | Sra);
                let rotate = matches!(op, Rol | Ror);
                // the rotation circuit is quadratic in the width: evaluate it at the widths that
                // used to abort in the bit-blaster
                let bb1 = rotate && matches!(w, 65 | 70 | 100 | 129);
                let circuit = (shift || bb1).then(|| Circuit::new(op, w));
                for (i, x) in vals.iter().enumerate() {
                    for (j, y) in vals.iter().enumerate() {
                        let blast = i == last
                            && if shift || bb1 {
                                true
                            } else if rotate {
                                j == last
                            } else {
                                w == 65 && j == 0
                            };
                        check(op, x, y, blast, circuit.as_ref());
                    }
                }
            }
        }
    }
}
