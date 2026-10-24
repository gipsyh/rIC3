//! Rewrite-rule audit (oss-toolchain G10-b): a mechanical semantic oracle for every word-level
//! rewrite rule in `src/fol/simplify.rs`.
//!
//! For every generated term `orig` the harness computes `simp = orig.simplify_with_ctx(level)` at
//! O0..O3 and checks
//!   1. `simulate(orig) == simulate(simp)` (word-level simulator, `src/fol/simulate.rs`),
//!   2. `simulate(bitblast(orig)) == simulate(orig)` (bit-blaster agrees with the simulator),
//!   3. `simulate(bitblast(simp)) == simulate(bitblast(orig))` (rewrite is sound at bit level),
//! exhaustively over all input values when the free variables have few bits, else by seeded random
//! sampling. Terms are built *raw* (`term_mgr().new_term`, no O0 simplification at construction)
//! so that the O0 rules are exercised by the oracle too.
//!
//! Generators: (i) generic random well-typed terms over all `FolOp`s, (ii) one targeted generator
//! per rule that builds the exact matched pattern (every branch) plus near-miss variants.
//!
//! Run (debug build, ~1-2 min):
//!   cargo +nightly-2026-09-30 test --test rewrite_audit -- --nocapture
//! Environment:
//!   LOGICRS_AUDIT_SEED=<u64>       PRNG seed (default 20261013)
//!   LOGICRS_AUDIT_SAMPLES=<n>      random samples per case at the random widths (default 64)
//!   LOGICRS_AUDIT_EXH_BITS=<n>     exhaustive when total free-variable bits <= n (default 10)
//!   LOGICRS_AUDIT_GENERIC=<n>      generic random terms per width (default 120)
//!   LOGICRS_AUDIT_BB_BUDGET=<n>    bit-blast cost budget per case (default 6000 gate-equivalents)
//!   LOGICRS_AUDIT_BB_SAMPLES=<n>   assignments checked at bit level per case (default 24)
//!   LOGICRS_AUDIT_OUT=<dir>        output directory (default target/rewrite_audit)
//!   LOGICRS_AUDIT_QUIET=1          no progress lines on stderr
//! Mismatch reproducers are written to `<out>/<n>.btor` (`bad = neq(orig, simp)`), the full
//! report to `<out>/report.txt`. The test fails on the classes rule, const-fold and
//! bitblast-vs-simulator; oracle limitations (simulator panics on variable operands) are listed.
//! A release build (`--release`) turns the overflow panics into silently wrong folded constants,
//! which the bit-level oracle then reports as RewriteMismatch.

mod common;

use common::btor2;
use giputils::bitvec::BitVec;
use giputils::hash::GHashMap;
use logicrs::fol::simplify::{SimplifyCtx, audit};
use logicrs::fol::{
    ArrayValue, FolOp, OpTerm, Sort, Term, TermType, TermVec, Value, term_gc, term_mgr,
};
use logicrs::{Lbool, LboolVec, OptLevel};
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashSet};
use std::fmt::Write as _;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

// ------------------------------------------------------------------------------------------------
// Rule inventory (keep in sync with `impl RewriteRule for <Name>` in src/fol/simplify.rs; the
// test `rule_list_in_sync` checks it against the source text).
// ------------------------------------------------------------------------------------------------

const RULES: &[&str] = &[
    // not
    "NotBoolXorEqSwap",
    "NotIteConst",
    // and
    "AndConstPropagation",
    "AndComplement",
    "AndBoolMask",
    "AndMergeNestedAnds",
    "AndDeMorganNotNot",
    "AndAbsorbComplementInOr",
    "AndDistributeOverOr",
    "AndMergeAdjacentEqSliceConsts",
    "AndBitLevelEqReconstruction",
    "AndBitLevelMaskedEqReconstruction",
    // or
    "OrConstPropagation",
    "OrComplement",
    "OrMergeNestedOrs",
    "OrDeMorganNotNot",
    "OrAbsorbComplementInAnd",
    "OrAbsorbIteCond",
    "OrMergeIteZeroBranches",
    "OrDistributeOverAnd",
    "OrMergeEqConstOneBitDiff",
    "OrMergeEqConstOneBitDiffAssoc",
    "OrBitLevelClauseReconstruction",
    "OrBitLevelMaskedClauseReconstruction",
    // xor
    "XorConstPropagation",
    "XorSelf",
    "XorComplement",
    // eq
    "EqBoolViaXor",
    "EqRefl",
    "EqComplement",
    "EqBoolMaskConst",
    "EqNotConst",
    "EqXorZero",
    "EqAndConst",
    // ult
    "UltConstX",
    "UltConstY",
    "UltConcatConst",
    // slt
    "SltRefl",
    "SltConstX",
    "SltConstY",
    "SltNonnegativeBound",
    // ite
    "IteConstCond",
    "IteSameBranches",
    "IteNotCondSwap",
    "IteNotBranches",
    "IteBoolComplementBranches",
    "IteBoolBranchConst",
    "IteSameCondNested",
    "IteNestedSharedBranch",
    "IteWriteBranches",
    // concat
    "ConcatConst",
    "ConcatAssocConstPrefix",
    "ConcatSignExtBySlice",
    "ConcatSignExtBySextSlice",
    "ConcatSignExtByMsbTerm",
    // sext
    "SextZeroExt",
    "SextBoolToIte",
    "SextMergeNested",
    // slice
    "SliceWholeRange",
    "SliceOfSlice",
    "SliceOfConcat",
    "SliceOfSext",
    "SliceOfIte",
    "SliceOfBitwiseOp",
    "SliceOfNeg",
    "SliceLsbOfAdd",
    "SliceLsbOfSll",
    // add / neg / mul
    "AddByZero",
    "NegBool",
    "MulByZero",
    "MulByOne",
    // read / write
    "ReadOverWriteSameIndex",
    "WriteSameValue",
    "WriteConditionalSameValue",
];

/// Rules that cannot fire through the public API, with the reason. The coverage check requires
/// 0 hits for these and >0 hits for every other rule; a stale entry fails the test either way.
const KNOWN_UNREACHABLE: &[(&str, &str)] = &[(
    "ConcatConst",
    "FolOp::simplify constant-folds any all-constant operand list before the pipeline runs",
)];

const EXHAUSTIVE_WIDTHS: &[usize] = &[1, 2, 3, 4, 5];
/// 65/70/129/140 sit beyond the simulator's `usize` shift and `u128`/`i128` division ranges.
const RANDOM_WIDTHS: &[usize] = &[8, 16, 31, 32, 33, 64, 65, 70, 129, 140];
const LEVELS: &[OptLevel] = &[OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

// ------------------------------------------------------------------------------------------------
// Deterministic PRNG (xorshift64*), independent of the `rand` crate API.
// ------------------------------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        debug_assert!(n > 0);
        (self.next() % n as u64) as usize
    }
    fn range(&mut self, lo: usize, hi_incl: usize) -> usize {
        lo + self.below(hi_incl - lo + 1)
    }
    fn chance(&mut self, num: usize, den: usize) -> bool {
        self.below(den) < num
    }
    fn bits(&mut self, w: usize) -> BitVec {
        (0..w).map(|_| self.next() & 1 == 1).collect()
    }
}

// ------------------------------------------------------------------------------------------------
// Raw term construction (no simplification at construction time).
// ------------------------------------------------------------------------------------------------

use FolOp::*;

/// Build `op(terms)` as a stored node without running `FolOp::simplify` (unlike `Term::new_op`).
fn raw(op: FolOp, terms: Vec<Term>) -> Term {
    assert!(
        op.is_core(),
        "{op:?} is not a core op; use Term::new_op (normalize)"
    );
    // the harness must only ever build well-typed terms; this guards the generators
    let w = |i: usize| terms[i].sort();
    match op {
        And | Or | Xor | Add | Mul | Udiv | Urem | Sdiv | Srem | Smod | Sll | Srl | Sra | Rol
        | Ror | Eq | Ult | Slt => {
            assert!(
                w(0) == w(1),
                "{op:?}: operand sorts differ: {:?} vs {:?}",
                w(0),
                w(1)
            )
        }
        Ite => assert!(
            w(0) == Sort::Bv(1) && w(1) == w(2),
            "Ite: cond {:?}, branches {:?} vs {:?}",
            w(0),
            w(1),
            w(2)
        ),
        Slice => {
            assert!(terms[2].bv_len() <= terms[1].bv_len() && terms[1].bv_len() < terms[0].bv_len())
        }
        Read => assert!(w(0).array().0 == w(1).bv()),
        Write => assert!(w(0).array() == (w(1).bv(), w(2).bv())),
        _ => {}
    }
    let sort = op.sort(&terms);
    term_mgr().new_term(TermType::Op(OpTerm { op, terms }), sort)
}

/// Dummy constant whose *width* encodes a slice bound or an extension width.
fn dummy(w: usize) -> Term {
    Term::bv_const(BitVec::zero(w))
}

fn r1(op: FolOp, a: &Term) -> Term {
    raw(op, vec![a.clone()])
}
fn r2(op: FolOp, a: &Term, b: &Term) -> Term {
    raw(op, vec![a.clone(), b.clone()])
}
fn not(a: &Term) -> Term {
    r1(Not, a)
}
fn neg(a: &Term) -> Term {
    r1(Neg, a)
}
fn and(a: &Term, b: &Term) -> Term {
    r2(And, a, b)
}
fn or(a: &Term, b: &Term) -> Term {
    r2(Or, a, b)
}
fn xor(a: &Term, b: &Term) -> Term {
    r2(Xor, a, b)
}
fn eq(a: &Term, b: &Term) -> Term {
    r2(Eq, a, b)
}
fn ult(a: &Term, b: &Term) -> Term {
    r2(Ult, a, b)
}
fn slt(a: &Term, b: &Term) -> Term {
    r2(Slt, a, b)
}
fn add(a: &Term, b: &Term) -> Term {
    r2(Add, a, b)
}
fn mul(a: &Term, b: &Term) -> Term {
    r2(Mul, a, b)
}
fn sll(a: &Term, b: &Term) -> Term {
    r2(Sll, a, b)
}
fn ite(c: &Term, t: &Term, e: &Term) -> Term {
    raw(Ite, vec![c.clone(), t.clone(), e.clone()])
}
/// `concat(hi, lo)`
fn cat(hi: &Term, lo: &Term) -> Term {
    r2(Concat, hi, lo)
}
/// `sext(x, e)`: extend by `e` bits
fn sext(x: &Term, e: usize) -> Term {
    raw(Sext, vec![x.clone(), dummy(e)])
}
/// `slice(x, l..=h)` (inclusive, `h >= l`)
fn sl(x: &Term, l: usize, h: usize) -> Term {
    assert!(
        l <= h && h < x.bv_len(),
        "slice {l}..={h} of a {}-bit term",
        x.bv_len()
    );
    raw(Slice, vec![x.clone(), dummy(h), dummy(l)])
}
fn bit(x: &Term, i: usize) -> Term {
    sl(x, i, i)
}
fn rd(a: &Term, i: &Term) -> Term {
    r2(Read, a, i)
}
fn wr(a: &Term, i: &Term, v: &Term) -> Term {
    raw(Write, vec![a.clone(), i.clone(), v.clone()])
}

fn bv_zero(w: usize) -> Term {
    Term::bv_const(BitVec::zero(w))
}
fn bv_one(w: usize) -> Term {
    Term::bv_const(BitVec::one(w))
}
fn bv_ones(w: usize) -> Term {
    Term::bv_const(BitVec::ones(w))
}
/// most negative signed value: only the msb set
fn bv_min(w: usize) -> Term {
    let mut c = BitVec::zero(w);
    c.set(w - 1, true);
    Term::bv_const(c)
}
/// most positive signed value: all but the msb set
fn bv_max(w: usize) -> Term {
    let mut c = BitVec::ones(w);
    c.set(w - 1, false);
    Term::bv_const(c)
}
fn bv_bit(w: usize, i: usize) -> BitVec {
    let mut c = BitVec::zero(w);
    c.set(i, true);
    c
}
fn var(w: usize) -> Term {
    Term::new_var(Sort::Bv(w))
}
fn boolvar() -> Term {
    var(1)
}

fn node_count(t: &Term) -> usize {
    fn go(t: &Term, seen: &mut HashSet<usize>) -> usize {
        if !seen.insert(t.id()) {
            return 0;
        }
        match &**t {
            TermType::Op(o) => 1 + o.terms.iter().map(|s| go(s, seen)).sum::<usize>(),
            _ => 1,
        }
    }
    go(t, &mut HashSet::new())
}

/// Free variables of a term DAG, ordered by id.
fn free_vars(t: &Term) -> Vec<Term> {
    fn go(t: &Term, seen: &mut HashSet<usize>, out: &mut Vec<Term>) {
        if !seen.insert(t.id()) {
            return;
        }
        match &**t {
            TermType::Var(_) => out.push(t.clone()),
            TermType::Op(o) => o.terms.iter().for_each(|s| go(s, seen, out)),
            TermType::Const(_) => {}
        }
    }
    let mut out = Vec::new();
    go(t, &mut HashSet::new(), &mut out);
    out.sort_by_key(|v| v.id());
    out
}

/// All operator sub-terms of `t` (excluding `t`), smallest first.
fn sub_ops(t: &Term) -> Vec<Term> {
    fn go(t: &Term, seen: &mut HashSet<usize>, out: &mut Vec<Term>) {
        if !seen.insert(t.id()) {
            return;
        }
        if let TermType::Op(o) = &**t {
            o.terms.iter().for_each(|s| go(s, seen, out));
            out.push(t.clone());
        }
    }
    let mut out = Vec::new();
    go(t, &mut HashSet::new(), &mut out);
    out.pop(); // t itself
    out.sort_by_key(node_count);
    out
}

/// Rough bit-level gate count of a DAG, to bound the bit-blast oracle.
fn bitblast_cost(t: &Term) -> usize {
    fn go(t: &Term, seen: &mut HashSet<usize>) -> usize {
        if !seen.insert(t.id()) {
            return 0;
        }
        let TermType::Op(o) = &**t else {
            return 0;
        };
        let w = match t.sort() {
            Sort::Bv(w) => w,
            Sort::Array(i, e) => (1usize << i) * e,
        };
        let own = match o.op {
            Mul | Udiv | Urem | Sdiv | Srem | Smod => w * w * 8,
            Sll | Srl | Sra | Rol | Ror => w * (usize::BITS - w.leading_zeros()) as usize * 2 + w,
            Read | Write => w * 3,
            _ => w,
        };
        own + o.terms.iter().map(|s| go(s, seen)).sum::<usize>()
    }
    go(t, &mut HashSet::new())
}

// ------------------------------------------------------------------------------------------------
// Values and assignments
// ------------------------------------------------------------------------------------------------

fn lbv_from_fn(w: usize, f: &dyn Fn(usize) -> bool) -> LboolVec {
    let mut v = LboolVec::from_elem(Lbool::FALSE, w);
    for i in 0..w {
        v.set_bool(i, f(i));
    }
    v
}

fn value_from_fn(sort: Sort, f: &dyn Fn(usize) -> bool) -> Value {
    match sort {
        Sort::Bv(w) => Value::Bv(lbv_from_fn(w, f)),
        Sort::Array(iw, ew) => {
            let mut a = ArrayValue::default_from(sort);
            for j in 0..(1usize << iw) {
                a.insert(j, lbv_from_fn(ew, &|i| f(j * ew + i)));
            }
            Value::Array(a)
        }
    }
}

fn sort_bits(s: Sort) -> usize {
    match s {
        Sort::Bv(w) => w,
        Sort::Array(i, e) => (1usize << i) * e,
    }
}

type Assignment = Vec<(Term, Value)>;

/// The `n`-th of the `2^bits` exhaustive assignments.
fn exhaustive_assignment(vars: &[Term], n: u64) -> Assignment {
    let mut off = 0;
    vars.iter()
        .map(|v| {
            let s = v.sort();
            let o = off;
            off += sort_bits(s);
            (v.clone(), value_from_fn(s, &|i| (n >> (o + i)) & 1 == 1))
        })
        .collect()
}

fn random_bv(rng: &mut Rng, w: usize) -> BitVec {
    match rng.below(10) {
        0 => BitVec::zero(w),
        1 => BitVec::ones(w),
        2 => BitVec::one(w),
        3 => bv_bit(w, w - 1),
        4 => {
            let mut c = BitVec::ones(w);
            c.set(w - 1, false);
            c
        }
        _ => rng.bits(w),
    }
}

fn random_assignment(rng: &mut Rng, vars: &[Term]) -> Assignment {
    vars.iter()
        .map(|v| {
            let s = v.sort();
            let val = match s {
                Sort::Bv(w) => Value::Bv(random_bv(rng, w).into()),
                Sort::Array(iw, ew) => {
                    let mut a = ArrayValue::default_from(s);
                    for j in 0..(1usize << iw) {
                        a.insert(j, random_bv(rng, ew).into());
                    }
                    Value::Array(a)
                }
            };
            (v.clone(), val)
        })
        .collect()
}

fn show_lbv(v: &LboolVec) -> String {
    (0..v.len())
        .rev()
        .map(|i| match v.get(i) {
            l if l.is_true() => '1',
            l if l.is_false() => '0',
            _ => 'x',
        })
        .collect()
}

fn show_value(v: &Value) -> String {
    match v {
        Value::Bv(b) => show_lbv(b),
        Value::Array(a) => {
            let mut idx: Vec<_> = a.keys().copied().collect();
            idx.sort();
            let parts: Vec<String> = idx
                .iter()
                .map(|i| format!("[{i}]={}", show_lbv(&a[i])))
                .collect();
            format!("{{{}}}", parts.join(" "))
        }
    }
}

fn show_assignment(a: &Assignment) -> String {
    a.iter()
        .enumerate()
        .map(|(k, (v, val))| format!("x{k}({:?})={}", v.sort(), show_value(val)))
        .collect::<Vec<_>>()
        .join(" ")
}

/// First position where `exp` is defined and `got` differs or is X. `exp` X bits are don't-care
/// (the simulator yields X for division by zero and for unwritten array cells).
fn cmp_lbv(exp: &LboolVec, got: &LboolVec) -> Option<String> {
    if exp.len() != got.len() {
        return Some(format!("width {} vs {}", exp.len(), got.len()));
    }
    for i in 0..exp.len() {
        let e = exp.get(i);
        if e.is_none() {
            continue;
        }
        let g = got.get(i);
        if g.is_none() || g != e {
            return Some(format!("bit {i}: expected {e} got {g}"));
        }
    }
    None
}

fn cmp_value(exp: &Value, got: &Value) -> Option<String> {
    match (exp, got) {
        (Value::Bv(e), Value::Bv(g)) => cmp_lbv(e, g),
        (Value::Array(e), Value::Array(g)) => {
            let ew = e.sort().array().1;
            let mut keys: Vec<usize> = e.keys().chain(g.keys()).copied().collect();
            keys.sort();
            keys.dedup();
            let x = LboolVec::from_elem(Lbool::NONE, ew);
            for k in keys {
                let ev = e.get(&k).unwrap_or(&x);
                let gv = g.get(&k).unwrap_or(&x);
                if let Some(d) = cmp_lbv(ev, gv) {
                    return Some(format!("[{k}] {d}"));
                }
            }
            None
        }
        _ => Some("sort mismatch (bv vs array)".into()),
    }
}

/// Bits of a word-level value in bit-blast order (bv: bit i; array: element j bit i at j*ew+i).
fn value_bits(v: &Value, sort: Sort) -> Vec<Lbool> {
    match (v, sort) {
        (Value::Bv(b), _) => (0..b.len()).map(|i| b.get(i)).collect(),
        (Value::Array(a), Sort::Array(iw, ew)) => {
            let mut out = Vec::with_capacity((1 << iw) * ew);
            for j in 0..(1usize << iw) {
                match a.get(&j) {
                    Some(e) => out.extend((0..ew).map(|i| e.get(i))),
                    None => out.extend(std::iter::repeat_n(Lbool::NONE, ew)),
                }
            }
            out
        }
        _ => unreachable!(),
    }
}

fn cmp_bits(exp: &[Lbool], got: &[Lbool]) -> Option<String> {
    if exp.len() != got.len() {
        return Some(format!("width {} vs {}", exp.len(), got.len()));
    }
    for (i, (e, g)) in exp.iter().zip(got).enumerate() {
        if e.is_none() {
            continue;
        }
        if g.is_none() || g != e {
            return Some(format!("bit {i}: expected {e} got {g}"));
        }
    }
    None
}

// ------------------------------------------------------------------------------------------------
// Panic capture (rules or the simulator may panic on an edge case; that is a finding, not a stop)
// ------------------------------------------------------------------------------------------------

thread_local! {
    static CAPTURING: Cell<bool> = const { Cell::new(false) };
    static LAST_PANIC: RefCell<String> = const { RefCell::new(String::new()) };
}

fn install_panic_hook() {
    let default = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if CAPTURING.with(|c| c.get()) {
            let msg = info
                .payload()
                .downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| info.payload().downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "<non-string panic>".into());
            let loc = info
                .location()
                .map(|l| format!("{}:{}", l.file(), l.line()))
                .unwrap_or_default();
            LAST_PANIC.with(|p| *p.borrow_mut() = format!("{msg} ({loc})"));
        } else {
            default(info);
        }
    }));
}

fn guarded<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    CAPTURING.with(|c| c.set(true));
    let r = catch_unwind(AssertUnwindSafe(f));
    CAPTURING.with(|c| c.set(false));
    r.map_err(|_| LAST_PANIC.with(|p| p.borrow().clone()))
}

// ------------------------------------------------------------------------------------------------
// Configuration and findings
// ------------------------------------------------------------------------------------------------

#[derive(Clone)]
struct Cfg {
    seed: u64,
    samples: usize,
    exh_bits: usize,
    generic_per_width: usize,
    bb_budget: usize,
    bb_samples: usize,
}

fn env_num(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

impl Cfg {
    fn from_env() -> Self {
        Cfg {
            seed: env_num("LOGICRS_AUDIT_SEED", 20261013),
            samples: env_num("LOGICRS_AUDIT_SAMPLES", 64) as usize,
            exh_bits: env_num("LOGICRS_AUDIT_EXH_BITS", 10) as usize,
            generic_per_width: env_num("LOGICRS_AUDIT_GENERIC", 120) as usize,
            bb_budget: env_num("LOGICRS_AUDIT_BB_BUDGET", 6000) as usize,
            bb_samples: env_num("LOGICRS_AUDIT_BB_SAMPLES", 24) as usize,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Kind {
    /// `simplify_with_ctx` panicked
    SimplifyPanic,
    /// the simulator or the bit-blaster panicked on `orig` or `simp`
    OraclePanic,
    /// simulate(orig) != simulate(simp): rewrite changed the function
    RewriteMismatch,
    /// simulate(bitblast(simp)) != simulate(bitblast(orig)) but the word-level simulator agreed
    BitblastRewriteMismatch,
    /// simulate(bitblast(orig)) != simulate(orig): bit-blaster and simulator disagree (not a rule)
    BitblastSimMismatch,
}

#[derive(Clone)]
struct Finding {
    kind: Kind,
    case: String,
    level: OptLevel,
    orig: Term,
    simp: Option<Term>,
    fired: Vec<&'static str>,
    assignment: String,
    detail: String,
}

impl Finding {
    fn size(&self) -> usize {
        let vars = free_vars(&self.orig);
        let bits: usize = vars.iter().map(|v| sort_bits(v.sort())).sum();
        bits * 1000 + node_count(&self.orig)
    }
    fn render(&self, n: usize, btor: Option<&str>) -> String {
        let mut s = String::new();
        let _ = writeln!(
            s,
            "#{n} {:?} case={} level={:?}",
            self.kind, self.case, self.level
        );
        let _ = writeln!(s, "  orig : {:?}", self.orig);
        if let Some(sp) = &self.simp {
            let _ = writeln!(s, "  simp : {sp:?}");
        }
        let _ = writeln!(s, "  fired: {:?}", self.fired);
        let _ = writeln!(s, "  input: {}", self.assignment);
        let _ = writeln!(s, "  {}", self.detail);
        if let Some(p) = btor {
            let _ = writeln!(s, "  btor2: {p}");
        }
        s
    }
}

struct Case {
    name: String,
    orig: Term,
}

// ------------------------------------------------------------------------------------------------
// Generic random term generator over all FolOps
// ------------------------------------------------------------------------------------------------

struct GenericGen<'a> {
    rng: &'a mut Rng,
    /// base width of the variable pool
    w: usize,
    vars: Vec<Term>,
    bools: Vec<Term>,
}

impl GenericGen<'_> {
    fn const_of(&mut self, w: usize) -> Term {
        Term::bv_const(random_bv(self.rng, w))
    }

    fn leaf(&mut self, w: usize) -> Term {
        if self.rng.chance(1, 4) {
            return self.const_of(w);
        }
        if w == 1 && self.rng.chance(1, 2) {
            let i = self.rng.below(self.bools.len());
            return self.bools[i].clone();
        }
        let base = self.vars[self.rng.below(self.vars.len())].clone();
        let bw = self.w;
        if w == bw {
            base
        } else if w < bw {
            let l = self.rng.below(bw - w + 1);
            sl(&base, l, l + w - 1)
        } else {
            match self.rng.below(3) {
                0 => {
                    let c = self.const_of(w - bw);
                    cat(&c, &base)
                }
                1 => sext(&base, w - bw),
                _ => Term::new_op(Uext, [base, dummy(w - bw)]),
            }
        }
    }

    fn bv(&mut self, w: usize, depth: usize) -> Term {
        if depth == 0 || self.rng.chance(1, 6) {
            return self.leaf(w);
        }
        let d = depth - 1;
        let mut choices: Vec<u8> = vec![0, 0, 0, 1, 2, 3, 6];
        if w >= 2 {
            choices.extend([4, 5]);
        }
        if w == 1 {
            choices.extend([7, 7]);
        }
        match choices[self.rng.below(choices.len())] {
            0 => {
                const OPS: [FolOp; 15] = [
                    And, Or, Xor, Sll, Srl, Sra, Rol, Ror, Add, Mul, Udiv, Urem, Sdiv, Srem, Smod,
                ];
                let op = OPS[self.rng.below(OPS.len())];
                let a = self.bv(w, d);
                let b = self.bv(w, d);
                raw(op, vec![a, b])
            }
            1 => {
                let a = self.bv(w, d);
                if self.rng.chance(1, 2) {
                    not(&a)
                } else {
                    neg(&a)
                }
            }
            2 => {
                let c = self.bv(1, d);
                let t = self.bv(w, d);
                let e = self.bv(w, d);
                ite(&c, &t, &e)
            }
            3 => {
                const OPS: [FolOp; 6] = [Sub, Nand, Nor, Xnor, Inc, Dec];
                let op = OPS[self.rng.below(OPS.len())];
                let a = self.bv(w, d);
                if op.num_operand() == 1 {
                    Term::new_op(op, [a])
                } else {
                    let b = self.bv(w, d);
                    Term::new_op(op, [a, b])
                }
            }
            4 => {
                let a = self.rng.range(1, w - 1);
                let hi = self.bv(a, d);
                let lo = self.bv(w - a, d);
                cat(&hi, &lo)
            }
            5 => {
                let a = self.rng.range(1, w - 1);
                let x = self.bv(a, d);
                if self.rng.chance(1, 2) {
                    sext(&x, w - a)
                } else {
                    Term::new_op(Uext, [x, dummy(w - a)])
                }
            }
            6 => {
                let iw = w + self.rng.range(0, 3);
                let l = self.rng.below(iw - w + 1);
                let x = self.bv(iw, d);
                sl(&x, l, l + w - 1)
            }
            7 => {
                let u = self.rng.range(1, self.w);
                if self.rng.chance(1, 4) {
                    const OPS: [FolOp; 3] = [Redxor, Redand, Redor];
                    let op = OPS[self.rng.below(OPS.len())];
                    let a = self.bv(u, d);
                    return if op.is_core() {
                        raw(op, vec![a])
                    } else {
                        Term::new_op(op, [a])
                    };
                }
                const OPS: [FolOp; 13] = [
                    Eq, Ult, Slt, Neq, Ugt, Ulte, Ugte, Sgt, Slte, Sgte, Iff, Implies, Udivo,
                ];
                let op = OPS[self.rng.below(OPS.len())];
                // Implies normalizes to the bitwise `!a | b` (sort of `a`): only well-typed on bools
                let u = if op == Implies { 1 } else { u };
                let a = self.bv(u, d);
                let b = self.bv(u, d);
                if op.is_core() {
                    raw(op, vec![a, b])
                } else {
                    Term::new_op(op, [a, b])
                }
            }
            _ => unreachable!(),
        }
    }
}

fn generic_case(rng: &mut Rng, w: usize, k: usize) -> Case {
    let nvars = rng.range(1, 3);
    let vars: Vec<Term> = (0..nvars).map(|_| var(w)).collect();
    let bools: Vec<Term> = (0..2).map(|_| boolvar()).collect();
    let depth = rng.range(2, 4);
    let out_w = if rng.chance(1, 3) { 1 } else { w };
    let mut g = GenericGen {
        rng,
        w,
        vars,
        bools,
    };
    let orig = g.bv(out_w, depth);
    Case {
        name: format!("generic/w{w}/{k}/d{depth}"),
        orig,
    }
}

/// Random nest of Write / Ite / Read over one array variable.
fn generic_array_case(rng: &mut Rng, w: usize, k: usize) -> Case {
    let iw = rng.range(1, 2);
    let ew = w.min(8);
    let a = Term::new_var(Sort::Array(iw, ew));
    let idx: Vec<Term> = (0..2).map(|_| var(iw)).collect();
    let vals: Vec<Term> = (0..2).map(|_| var(ew)).collect();
    let conds: Vec<Term> = (0..2).map(|_| boolvar()).collect();
    let mut t = a.clone();
    let steps = rng.range(1, 3);
    for _ in 0..steps {
        let i = if rng.chance(1, 4) {
            Term::bv_const(rng.bits(iw))
        } else {
            idx[rng.below(2)].clone()
        };
        let c = conds[rng.below(2)].clone();
        let v = match rng.below(5) {
            0 => Term::bv_const(rng.bits(ew)),
            1 => rd(&t, &i),
            2 => {
                let r = rd(&a, &i);
                let v = vals[rng.below(2)].clone();
                if rng.chance(1, 2) {
                    ite(&c, &r, &v)
                } else {
                    ite(&c, &v, &r)
                }
            }
            _ => vals[rng.below(2)].clone(),
        };
        t = match rng.below(4) {
            0 => ite(&c, &wr(&t, &i, &v), &t),
            1 => ite(&c, &t, &wr(&t, &i, &v)),
            2 => ite(&c, &wr(&t, &i, &v), &wr(&t, &i, &vals[rng.below(2)])),
            _ => wr(&t, &i, &v),
        };
    }
    let orig = if rng.chance(1, 2) {
        let i = idx[rng.below(2)].clone();
        rd(&t, &i)
    } else {
        t
    };
    Case {
        name: format!("generic-array/w{w}/{k}"),
        orig,
    }
}

// ------------------------------------------------------------------------------------------------
// Targeted generators: one per rule, every branch of the rule's `apply` plus near-miss variants.
// ------------------------------------------------------------------------------------------------

struct Ctx<'a> {
    rng: &'a mut Rng,
    w: usize,
}

type Variants = Vec<(&'static str, Term)>;
type Gen = fn(&mut Ctx) -> Variants;

impl Ctx<'_> {
    fn v(&self) -> Term {
        var(self.w)
    }
    fn k(&mut self) -> Term {
        Term::bv_const(random_bv(self.rng, self.w))
    }
    fn kw(&mut self, w: usize) -> Term {
        Term::bv_const(random_bv(self.rng, w))
    }
    /// a random constant that is neither all-zero nor all-ones (needs w >= 2)
    fn k_mid(&mut self) -> Term {
        loop {
            let c = random_bv(self.rng, self.w);
            if !c.is_zero() && !c.is_ones() {
                return Term::bv_const(c);
            }
        }
    }
    fn arr(&self) -> (Term, Term, Term) {
        let iw = self.w.min(2);
        let a = Term::new_var(Sort::Array(iw, self.w));
        (a, var(iw), var(iw))
    }
}

/// `x[i]` or `!x[i]`
fn lit(x: &Term, i: usize, pos: bool) -> Term {
    if pos { bit(x, i) } else { not(&bit(x, i)) }
}

fn gen_not_bool_xor_eq_swap(c: &mut Ctx) -> Variants {
    let (b, d, x, y) = (boolvar(), boolvar(), c.v(), c.v());
    let mut v = vec![("xor", not(&xor(&b, &d))), ("eq", not(&eq(&b, &d)))];
    if c.w > 1 {
        v.push(("near-xor-wide", not(&xor(&x, &y))));
        v.push(("near-eq-wide-operands", not(&eq(&x, &y))));
    }
    v
}

fn gen_not_ite_const(c: &mut Ctx) -> Variants {
    let (b, x, k1, k2) = (boolvar(), c.v(), c.k(), c.k());
    vec![
        ("consts", not(&ite(&b, &k1, &k2))),
        ("near-one-const", not(&ite(&b, &k1, &x))),
    ]
}

fn gen_and_const_propagation(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let mut v = vec![
        ("ones-x", and(&bv_ones(w), &x)),
        ("zero-x", and(&bv_zero(w), &x)),
        ("x-ones", and(&x, &bv_ones(w))),
        ("x-zero", and(&x, &bv_zero(w))),
    ];
    if w > 1 {
        v.push(("near-mid-const", and(&c.k_mid(), &x)));
    }
    v
}

fn gen_and_complement(c: &mut Ctx) -> Variants {
    let (x, y) = (c.v(), c.v());
    vec![
        ("x-notx", and(&x, &not(&x))),
        ("notx-x", and(&not(&x), &x)),
        ("near-other", and(&x, &not(&y))),
    ]
}

fn gen_and_bool_mask(c: &mut Ctx) -> Variants {
    let (x, b, w) = (c.v(), boolvar(), c.w);
    let pos = ite(&b, &bv_ones(w), &bv_zero(w));
    let negm = ite(&b, &bv_zero(w), &bv_ones(w));
    let mut v = vec![
        ("pos", and(&x, &pos)),
        ("neg", and(&x, &negm)),
        ("pos-swapped", and(&pos, &x)),
    ];
    if w > 1 {
        let k = c.k_mid();
        v.push(("near-not-mask", and(&x, &ite(&b, &bv_ones(w), &k))));
    }
    v
}

fn gen_and_merge_nested_ands(c: &mut Ctx) -> Variants {
    let (x, y, z) = (c.v(), c.v(), c.v());
    vec![
        ("xy-y", and(&and(&x, &y), &y)),
        ("xy-x", and(&and(&x, &y), &x)),
        ("y-xy", and(&y, &and(&x, &y))),
        ("xy-xz", and(&and(&x, &y), &and(&x, &z))),
        ("xy-zx", and(&and(&x, &y), &and(&z, &x))),
        ("yx-xz", and(&and(&y, &x), &and(&x, &z))),
        ("yx-zx", and(&and(&y, &x), &and(&z, &x))),
        ("near-xy-z", and(&and(&x, &y), &z)),
    ]
}

fn gen_and_demorgan_not_not(c: &mut Ctx) -> Variants {
    let (x, y) = (c.v(), c.v());
    vec![
        ("notx-noty", and(&not(&x), &not(&y))),
        ("near-notx-y", and(&not(&x), &y)),
    ]
}

fn gen_and_absorb_complement_in_or(c: &mut Ctx) -> Variants {
    let (x, y, z) = (c.v(), c.v(), c.v());
    vec![
        ("x-or(notx,y)", and(&x, &or(&not(&x), &y))),
        ("x-or(y,notx)", and(&x, &or(&y, &not(&x)))),
        ("notx-or(x,y)", and(&not(&x), &or(&x, &y))),
        ("notx-or(y,x)", and(&not(&x), &or(&y, &x))),
        ("swapped", and(&or(&not(&x), &y), &x)),
        ("near-other-var", and(&x, &or(&not(&y), &z))),
    ]
}

fn gen_and_distribute_over_or(c: &mut Ctx) -> Variants {
    let (x, y, z, u) = (c.v(), c.v(), c.v(), c.v());
    vec![
        ("or(x,y)-x", and(&or(&x, &y), &x)),
        ("or(x,y)-y", and(&or(&x, &y), &y)),
        ("x-or(x,y)", and(&x, &or(&x, &y))),
        ("or(x,y)-or(x,z)", and(&or(&x, &y), &or(&x, &z))),
        ("or(x,y)-or(z,x)", and(&or(&x, &y), &or(&z, &x))),
        ("or(y,x)-or(x,z)", and(&or(&y, &x), &or(&x, &z))),
        ("or(y,x)-or(z,x)", and(&or(&y, &x), &or(&z, &x))),
        ("near-disjoint", and(&or(&x, &y), &or(&z, &u))),
    ]
}

fn gen_and_merge_adjacent_eq_slice_consts(c: &mut Ctx) -> Variants {
    let w = c.w;
    if w < 2 {
        return vec![];
    }
    let (x, y) = (c.v(), c.v());
    let m = c.rng.range(1, w - 1);
    let (k1, k2) = (c.kw(m), c.kw(w - m));
    let a = eq(&sl(&x, 0, m - 1), &k1);
    let b = eq(&sl(&x, m, w - 1), &k2);
    let mut v = vec![
        ("lo-hi", and(&a, &b)),
        ("hi-lo", and(&b, &a)),
        ("const-first", and(&eq(&k1, &sl(&x, 0, m - 1)), &b)),
        ("near-other-base", and(&a, &eq(&sl(&y, m, w - 1), &k2))),
    ];
    if w >= 3 {
        let (g1, g2) = (c.kw(1), c.kw(w - 2));
        v.push((
            "near-gap",
            and(&eq(&sl(&x, 0, 0), &g1), &eq(&sl(&x, 2, w - 1), &g2)),
        ));
        let (o1, o2) = (c.kw(2), c.kw(w - 1));
        v.push((
            "near-overlap",
            and(&eq(&sl(&x, 0, 1), &o1), &eq(&sl(&x, 1, w - 1), &o2)),
        ));
    }
    v
}

fn gen_and_bit_level_eq_reconstruction(c: &mut Ctx) -> Variants {
    let w = c.w;
    if w < 2 {
        return vec![];
    }
    let (x, y) = (c.v(), c.v());
    let mut v = vec![
        ("x0-!x1", and(&lit(&x, 0, true), &lit(&x, 1, false))),
        ("!x1-x0", and(&lit(&x, 1, false), &lit(&x, 0, true))),
        ("x1-x0", and(&bit(&x, 1), &bit(&x, 0))),
        ("near-other-base", and(&bit(&x, 0), &bit(&y, 1))),
    ];
    if w >= 3 {
        v.push((
            "nested-3",
            and(&and(&bit(&x, 2), &bit(&x, 0)), &lit(&x, 1, false)),
        ));
        v.push((
            "conflict",
            and(&and(&bit(&x, 0), &bit(&x, 2)), &not(&bit(&x, 0))),
        ));
        v.push(("near-gap", and(&bit(&x, 0), &bit(&x, 2))));
    }
    v
}

/// chain of `n` bit literals of `x` at the given indices, built so no contiguous prefix exists
fn lit_chain(c: &mut Ctx, op: FolOp, x: &Term, idx: &[usize]) -> Term {
    let mut t = lit(x, idx[0], c.rng.chance(1, 2));
    for &i in &idx[1..] {
        let l = lit(x, i, c.rng.chance(1, 2));
        t = r2(op, &t, &l);
    }
    t
}

fn gen_and_bit_level_masked_eq_reconstruction(c: &mut Ctx) -> Variants {
    let w = c.w;
    if w < 10 {
        return vec![];
    }
    let x = c.v();
    let mut v = vec![
        ("8-gap", lit_chain(c, And, &x, &[8, 0, 1, 2, 3, 4, 5, 6])),
        ("near-7-gap", lit_chain(c, And, &x, &[8, 0, 1, 2, 3, 4, 5])),
    ];
    if w >= 16 {
        v.push((
            "8-sparse",
            lit_chain(c, And, &x, &[0, 2, 4, 6, 8, 10, 12, 14]),
        ));
        v.push((
            "9-sparse",
            lit_chain(c, And, &x, &[0, 2, 4, 6, 8, 10, 12, 14, 15]),
        ));
    }
    v
}

fn gen_or_const_propagation(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let mut v = vec![
        ("ones-x", or(&bv_ones(w), &x)),
        ("zero-x", or(&bv_zero(w), &x)),
        ("x-ones", or(&x, &bv_ones(w))),
        ("x-zero", or(&x, &bv_zero(w))),
    ];
    if w > 1 {
        v.push(("near-mid-const", or(&c.k_mid(), &x)));
    }
    v
}

fn gen_or_complement(c: &mut Ctx) -> Variants {
    let (x, y) = (c.v(), c.v());
    vec![
        ("x-notx", or(&x, &not(&x))),
        ("notx-x", or(&not(&x), &x)),
        ("near-other", or(&x, &not(&y))),
    ]
}

fn gen_or_merge_nested_ors(c: &mut Ctx) -> Variants {
    let (x, y, z) = (c.v(), c.v(), c.v());
    vec![
        ("xy-y", or(&or(&x, &y), &y)),
        ("xy-x", or(&or(&x, &y), &x)),
        ("y-xy", or(&y, &or(&x, &y))),
        ("xy-xz", or(&or(&x, &y), &or(&x, &z))),
        ("xy-zx", or(&or(&x, &y), &or(&z, &x))),
        ("yx-xz", or(&or(&y, &x), &or(&x, &z))),
        ("yx-zx", or(&or(&y, &x), &or(&z, &x))),
        ("near-xy-z", or(&or(&x, &y), &z)),
    ]
}

fn gen_or_demorgan_not_not(c: &mut Ctx) -> Variants {
    let (x, y) = (c.v(), c.v());
    vec![
        ("notx-noty", or(&not(&x), &not(&y))),
        ("near-notx-y", or(&not(&x), &y)),
    ]
}

fn gen_or_absorb_complement_in_and(c: &mut Ctx) -> Variants {
    let (x, y, z) = (c.v(), c.v(), c.v());
    vec![
        ("x-and(notx,y)", or(&x, &and(&not(&x), &y))),
        ("x-and(y,notx)", or(&x, &and(&y, &not(&x)))),
        ("notx-and(x,y)", or(&not(&x), &and(&x, &y))),
        ("notx-and(y,x)", or(&not(&x), &and(&y, &x))),
        ("swapped", or(&and(&not(&x), &y), &x)),
        ("near-other-var", or(&x, &and(&not(&y), &z))),
    ]
}

fn gen_or_distribute_over_and(c: &mut Ctx) -> Variants {
    let (x, y, z, u) = (c.v(), c.v(), c.v(), c.v());
    vec![
        ("and(x,y)-x", or(&and(&x, &y), &x)),
        ("and(x,y)-y", or(&and(&x, &y), &y)),
        ("x-and(x,y)", or(&x, &and(&x, &y))),
        ("and(x,y)-and(x,z)", or(&and(&x, &y), &and(&x, &z))),
        ("and(x,y)-and(z,x)", or(&and(&x, &y), &and(&z, &x))),
        ("and(y,x)-and(x,z)", or(&and(&y, &x), &and(&x, &z))),
        ("and(y,x)-and(z,x)", or(&and(&y, &x), &and(&z, &x))),
        ("near-disjoint", or(&and(&x, &y), &and(&z, &u))),
    ]
}

fn gen_or_absorb_ite_cond(_c: &mut Ctx) -> Variants {
    let (b, d, e, f) = (boolvar(), boolvar(), boolvar(), boolvar());
    vec![
        ("ite-c", or(&ite(&b, &d, &e), &b)),
        ("ite-notc", or(&ite(&b, &d, &e), &not(&b))),
        ("c-ite", or(&b, &ite(&b, &d, &e))),
        ("near-other-cond", or(&ite(&b, &d, &e), &f)),
    ]
}

fn gen_or_merge_ite_zero_branches(c: &mut Ctx) -> Variants {
    let (x, y, b, d, w) = (c.v(), c.v(), boolvar(), boolvar(), c.w);
    let z = bv_zero(w);
    vec![
        ("tf", or(&ite(&b, &x, &z), &ite(&b, &z, &y))),
        ("ft", or(&ite(&b, &z, &x), &ite(&b, &y, &z))),
        ("tt", or(&ite(&b, &x, &z), &ite(&b, &y, &z))),
        ("ff", or(&ite(&b, &z, &x), &ite(&b, &z, &y))),
        ("near-other-cond", or(&ite(&b, &x, &z), &ite(&d, &z, &y))),
    ]
}

fn gen_or_merge_eq_const_one_bit_diff(c: &mut Ctx) -> Variants {
    let (x, y, w) = (c.v(), c.v(), c.w);
    let mut v = Vec::new();
    let mut diffs = vec![0usize];
    if w >= 2 {
        diffs.push(w - 1);
    }
    if w >= 3 {
        diffs.push(w / 2);
    }
    for (n, d) in diffs.into_iter().enumerate() {
        let c1 = random_bv(c.rng, w);
        let c2 = &c1 ^ &bv_bit(w, d);
        let (t1, t2) = (Term::bv_const(c1.clone()), Term::bv_const(c2));
        let names = [
            ("diff-lsb", "diff-lsb-const-first"),
            ("diff-msb", "diff-msb-const-first"),
            ("diff-mid", "diff-mid-const-first"),
        ];
        v.push((names[n].0, or(&eq(&x, &t1), &eq(&x, &t2))));
        v.push((names[n].1, or(&eq(&t1, &x), &eq(&x, &t2))));
        if n == 0 {
            v.push(("near-other-var", or(&eq(&x, &t1), &eq(&y, &t2))));
        }
    }
    if w >= 2 {
        let c1 = random_bv(c.rng, w);
        let c2 = &(&c1 ^ &bv_bit(w, 0)) ^ &bv_bit(w, w - 1);
        v.push((
            "near-two-bits",
            or(&eq(&x, &Term::bv_const(c1)), &eq(&x, &Term::bv_const(c2))),
        ));
    }
    v
}

fn gen_or_merge_eq_const_one_bit_diff_assoc(c: &mut Ctx) -> Variants {
    let (x, y, w) = (c.v(), c.v(), c.w);
    let c1 = random_bv(c.rng, w);
    let c2 = &c1 ^ &bv_bit(w, c.rng.below(w));
    let (t1, t2, k) = (Term::bv_const(c1.clone()), Term::bv_const(c2), c.k());
    let mut v = vec![
        (
            "left-nested",
            or(&or(&eq(&x, &t1), &eq(&y, &k)), &eq(&x, &t2)),
        ),
        (
            "right-nested",
            or(&eq(&x, &t1), &or(&eq(&y, &k), &eq(&x, &t2))),
        ),
    ];
    if w >= 2 {
        let c3 = &(&c1 ^ &bv_bit(w, 0)) ^ &bv_bit(w, w - 1);
        v.push((
            "near-two-bits",
            or(&or(&eq(&x, &t1), &eq(&y, &k)), &eq(&x, &Term::bv_const(c3))),
        ));
    }
    v
}

fn gen_or_bit_level_clause_reconstruction(c: &mut Ctx) -> Variants {
    let w = c.w;
    if w < 2 {
        return vec![];
    }
    let (x, y) = (c.v(), c.v());
    let mut v = vec![
        ("x0-!x1", or(&lit(&x, 0, true), &lit(&x, 1, false))),
        ("!x1-x0", or(&lit(&x, 1, false), &lit(&x, 0, true))),
        ("!x1-!x0", or(&lit(&x, 1, false), &lit(&x, 0, false))),
        ("near-other-base", or(&bit(&x, 0), &bit(&y, 1))),
    ];
    if w >= 3 {
        v.push((
            "nested-3",
            or(&or(&bit(&x, 2), &bit(&x, 0)), &lit(&x, 1, false)),
        ));
        v.push((
            "conflict",
            or(&or(&bit(&x, 0), &bit(&x, 2)), &not(&bit(&x, 0))),
        ));
        v.push(("near-gap", or(&bit(&x, 0), &bit(&x, 2))));
    }
    v
}

fn gen_or_bit_level_masked_clause_reconstruction(c: &mut Ctx) -> Variants {
    let w = c.w;
    if w < 10 {
        return vec![];
    }
    let x = c.v();
    let mut v = vec![
        ("8-gap", lit_chain(c, Or, &x, &[8, 0, 1, 2, 3, 4, 5, 6])),
        ("near-7-gap", lit_chain(c, Or, &x, &[8, 0, 1, 2, 3, 4, 5])),
    ];
    if w >= 16 {
        v.push((
            "8-sparse",
            lit_chain(c, Or, &x, &[0, 2, 4, 6, 8, 10, 12, 14]),
        ));
        v.push((
            "9-sparse",
            lit_chain(c, Or, &x, &[0, 2, 4, 6, 8, 10, 12, 14, 15]),
        ));
    }
    v
}

fn gen_xor_const_propagation(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let mut v = vec![
        ("ones-x", xor(&bv_ones(w), &x)),
        ("zero-x", xor(&bv_zero(w), &x)),
        ("x-ones", xor(&x, &bv_ones(w))),
        ("x-zero", xor(&x, &bv_zero(w))),
    ];
    if w > 1 {
        v.push(("near-mid-const", xor(&c.k_mid(), &x)));
    }
    v
}

fn gen_xor_self(c: &mut Ctx) -> Variants {
    let (x, y) = (c.v(), c.v());
    vec![("x-x", xor(&x, &x)), ("near-x-y", xor(&x, &y))]
}

fn gen_xor_complement(c: &mut Ctx) -> Variants {
    let x = c.v();
    vec![("x-notx", xor(&x, &not(&x))), ("notx-x", xor(&not(&x), &x))]
}

fn gen_eq_bool_via_xor(_c: &mut Ctx) -> Variants {
    let (b, d) = (boolvar(), boolvar());
    let (t, f) = (Term::bool_const(true), Term::bool_const(false));
    vec![
        ("1-b", eq(&t, &b)),
        ("0-b", eq(&f, &b)),
        ("b-1", eq(&b, &t)),
        ("b-0", eq(&b, &f)),
        ("b-b", eq(&b, &b)),
        ("b-notb", eq(&b, &not(&b))),
        ("notb-b", eq(&not(&b), &b)),
        ("near-b-d", eq(&b, &d)),
    ]
}

fn gen_eq_refl(c: &mut Ctx) -> Variants {
    let (x, y) = (c.v(), c.v());
    vec![("x-x", eq(&x, &x)), ("near-x-y", eq(&x, &y))]
}

fn gen_eq_complement(c: &mut Ctx) -> Variants {
    let x = c.v();
    vec![("x-notx", eq(&x, &not(&x))), ("notx-x", eq(&not(&x), &x))]
}

fn gen_eq_bool_mask_const(c: &mut Ctx) -> Variants {
    let (b, w) = (boolvar(), c.w);
    let (o, z) = (bv_ones(w), bv_zero(w));
    let pos = ite(&b, &o, &z);
    let negm = ite(&b, &z, &o);
    let mut v = vec![
        ("pos-zero", eq(&pos, &z)),
        ("pos-ones", eq(&pos, &o)),
        ("neg-zero", eq(&negm, &z)),
        ("neg-ones", eq(&negm, &o)),
        ("zero-pos", eq(&z, &pos)),
    ];
    if w > 1 {
        let k = c.k_mid();
        v.push(("near-mid-const", eq(&pos, &k)));
    }
    v
}

fn gen_eq_not_const(c: &mut Ctx) -> Variants {
    let (x, y, k) = (c.v(), c.v(), c.k());
    vec![
        ("notx-noty", eq(&not(&x), &not(&y))),
        ("notx-c", eq(&not(&x), &k)),
        ("c-notx", eq(&k, &not(&x))),
        ("near-notx-y", eq(&not(&x), &y)),
    ]
}

fn gen_eq_xor_zero(c: &mut Ctx) -> Variants {
    let (x, y, w) = (c.v(), c.v(), c.w);
    vec![
        ("xor-zero", eq(&xor(&x, &y), &bv_zero(w))),
        ("zero-xor", eq(&bv_zero(w), &xor(&x, &y))),
        ("near-xor-ones", eq(&xor(&x, &y), &bv_ones(w))),
    ]
}

fn gen_eq_and_const(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let i = c.rng.below(w);
    let mut mask = random_bv(c.rng, w);
    mask.set(i, false);
    let mut k = random_bv(c.rng, w);
    k.set(i, true);
    let (mask_t, k_t) = (Term::bv_const(mask.clone()), Term::bv_const(k));
    // constant inside the mask: no fire
    let kin = Term::bv_const(&random_bv(c.rng, w) & &mask);
    vec![
        ("x-mask-c", eq(&and(&x, &mask_t), &k_t)),
        ("mask-x-c", eq(&and(&mask_t, &x), &k_t)),
        ("c-x-mask", eq(&k_t, &and(&x, &mask_t))),
        ("near-c-within-mask", eq(&and(&x, &mask_t), &kin)),
    ]
}

fn gen_ult_const_x(c: &mut Ctx) -> Variants {
    let (y, w) = (c.v(), c.w);
    let mut v = vec![
        ("zero-y", ult(&bv_zero(w), &y)),
        ("ones-y", ult(&bv_ones(w), &y)),
    ];
    if w > 1 {
        v.push(("near-mid", ult(&c.k_mid(), &y)));
    }
    v
}

fn gen_ult_const_y(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let mut v = vec![
        ("x-zero", ult(&x, &bv_zero(w))),
        ("x-ones", ult(&x, &bv_ones(w))),
    ];
    if w > 1 {
        v.push(("near-mid", ult(&x, &c.k_mid())));
    }
    v
}

fn gen_ult_concat_const(c: &mut Ctx) -> Variants {
    let w = c.w;
    if w < 2 {
        return vec![];
    }
    let hi = c.rng.range(1, w - 1);
    let lo = w - hi;
    let xs = var(lo);
    let zx = cat(&bv_zero(hi), &xs);
    let mut c_hi_nz = random_bv(c.rng, w);
    c_hi_nz.set(w - 1, true);
    let c_hi_z = {
        let mut k = random_bv(c.rng, w);
        for i in lo..w {
            k.set(i, false);
        }
        k
    };
    let (knz, kz) = (Term::bv_const(c_hi_nz), Term::bv_const(c_hi_z));
    vec![
        ("zx-ult-c-hi-nonzero", ult(&zx, &knz)),
        ("zx-ult-c-hi-zero", ult(&zx, &kz)),
        ("c-hi-nonzero-ult-zx", ult(&knz, &zx)),
        ("c-hi-zero-ult-zx", ult(&kz, &zx)),
        ("near-ones-prefix", ult(&cat(&bv_ones(hi), &xs), &kz)),
    ]
}

fn gen_slt_refl(c: &mut Ctx) -> Variants {
    let (x, y) = (c.v(), c.v());
    vec![("x-x", slt(&x, &x)), ("near-x-y", slt(&x, &y))]
}

fn gen_slt_const_x(c: &mut Ctx) -> Variants {
    let (y, w) = (c.v(), c.w);
    let mut v = vec![
        ("min-y", slt(&bv_min(w), &y)),
        ("max-y", slt(&bv_max(w), &y)),
    ];
    if w > 1 {
        v.push(("near-mid", slt(&c.k_mid(), &y)));
    }
    v
}

fn gen_slt_const_y(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let mut v = vec![
        ("x-min", slt(&x, &bv_min(w))),
        ("x-max", slt(&x, &bv_max(w))),
    ];
    if w > 1 {
        v.push(("near-mid", slt(&x, &c.k_mid())));
    }
    v
}

fn gen_slt_nonnegative_bound(c: &mut Ctx) -> Variants {
    let w = c.w;
    if w < 2 {
        return vec![];
    }
    let hi = c.rng.range(1, w - 1);
    let lo = w - hi;
    let xs = var(lo);
    let zx = cat(&bv_zero(hi), &xs);
    let mut v = vec![
        ("zero-bound", slt(&zx, &bv_zero(w))),
        ("neg-bound", slt(&zx, &bv_min(w))),
    ];
    let mut negk = random_bv(c.rng, w);
    negk.set(w - 1, true);
    v.push(("neg-random-bound", slt(&zx, &Term::bv_const(negk))));
    if w - 1 > lo {
        // a bit at index in lo..w-1 (not the sign bit)
        let mut k = random_bv(c.rng, w);
        k.set(w - 1, false);
        k.set(c.rng.range(lo, w - 2), true);
        v.push(("bound-above-range", slt(&zx, &Term::bv_const(k))));
    }
    let mut below = random_bv(c.rng, w);
    for i in lo..w {
        below.set(i, false);
    }
    v.push((
        "near-bound-within-range",
        slt(&zx, &Term::bv_const(below.clone())),
    ));
    v.push((
        "near-ones-prefix",
        slt(&cat(&bv_ones(hi), &xs), &bv_zero(w)),
    ));
    if w >= 3 && hi >= 2 {
        // sext(concat(0, xs), e) is still non-negative
        let e = 1;
        let inner = cat(&bv_zero(hi - e), &xs);
        v.push(("sext-zero-bound", slt(&sext(&inner, e), &bv_zero(w))));
        let mut k = random_bv(c.rng, w);
        k.set(w - 1, false);
        if w - 2 >= lo {
            k.set(w - 2, true);
        }
        v.push((
            "sext-bound-above",
            slt(&sext(&inner, e), &Term::bv_const(k)),
        ));
    }
    v
}

fn gen_ite_const_cond(c: &mut Ctx) -> Variants {
    let (x, y) = (c.v(), c.v());
    vec![
        ("true", ite(&Term::bool_const(true), &x, &y)),
        ("false", ite(&Term::bool_const(false), &x, &y)),
    ]
}

fn gen_ite_same_branches(c: &mut Ctx) -> Variants {
    let (x, y, b) = (c.v(), c.v(), boolvar());
    vec![("same", ite(&b, &x, &x)), ("near-diff", ite(&b, &x, &y))]
}

fn gen_ite_not_cond_swap(c: &mut Ctx) -> Variants {
    let (x, y, b) = (c.v(), c.v(), boolvar());
    vec![("not-cond", ite(&not(&b), &x, &y))]
}

fn gen_ite_not_branches(c: &mut Ctx) -> Variants {
    let (x, y, b) = (c.v(), c.v(), boolvar());
    vec![
        ("not-not", ite(&b, &not(&x), &not(&y))),
        ("neg-neg", ite(&b, &neg(&x), &neg(&y))),
        ("near-not-neg", ite(&b, &not(&x), &neg(&y))),
    ]
}

fn gen_ite_bool_complement_branches(_c: &mut Ctx) -> Variants {
    let (b, d) = (boolvar(), boolvar());
    vec![
        ("d-notd", ite(&b, &d, &not(&d))),
        ("notd-d", ite(&b, &not(&d), &d)),
    ]
}

fn gen_ite_bool_branch_const(_c: &mut Ctx) -> Variants {
    let (b, d) = (boolvar(), boolvar());
    let (t, f) = (Term::bool_const(true), Term::bool_const(false));
    vec![
        ("d-0", ite(&b, &d, &f)),
        ("d-1", ite(&b, &d, &t)),
        ("0-d", ite(&b, &f, &d)),
        ("1-d", ite(&b, &t, &d)),
    ]
}

fn gen_ite_same_cond_nested(c: &mut Ctx) -> Variants {
    let (x, y, z, b, d) = (c.v(), c.v(), c.v(), boolvar(), boolvar());
    vec![
        ("then-nested", ite(&b, &ite(&b, &x, &y), &z)),
        ("else-nested", ite(&b, &x, &ite(&b, &y, &z))),
        ("near-other-cond", ite(&b, &ite(&d, &x, &y), &z)),
    ]
}

fn gen_ite_nested_shared_branch(c: &mut Ctx) -> Variants {
    let (x, y, b, d) = (c.v(), c.v(), boolvar(), boolvar());
    vec![
        ("then-else-shared", ite(&b, &ite(&d, &x, &y), &y)),
        ("then-then-shared", ite(&b, &ite(&d, &y, &x), &y)),
        ("else-then-shared", ite(&b, &x, &ite(&d, &x, &y))),
        ("else-else-shared", ite(&b, &x, &ite(&d, &y, &x))),
    ]
}

fn gen_ite_write_branches(c: &mut Ctx) -> Variants {
    let (a, i, j) = c.arr();
    let (v1, v2, b) = (c.v(), c.v(), boolvar());
    let r = rd(&a, &i);
    vec![
        ("two-writes", ite(&b, &wr(&a, &i, &v1), &wr(&a, &i, &v2))),
        (
            "then-write-ite-read-else",
            ite(&b, &wr(&a, &i, &ite(&b, &v1, &r)), &a),
        ),
        (
            "then-write-ite-read-then",
            ite(&b, &wr(&a, &i, &ite(&b, &r, &v1)), &a),
        ),
        (
            "else-write-ite-read-then",
            ite(&b, &a, &wr(&a, &i, &ite(&b, &r, &v1))),
        ),
        (
            "else-write-ite-read-else",
            ite(&b, &a, &wr(&a, &i, &ite(&b, &v1, &r))),
        ),
        (
            "near-two-writes-diff-index",
            ite(&b, &wr(&a, &i, &v1), &wr(&a, &j, &v2)),
        ),
    ]
}

fn gen_concat_const(c: &mut Ctx) -> Variants {
    let (k1, k2) = (c.k(), c.k());
    vec![("consts", cat(&k1, &k2))]
}

fn gen_concat_assoc_const_prefix(c: &mut Ctx) -> Variants {
    let (x, k1, k2) = (c.v(), c.k(), c.k());
    vec![
        ("c1-c2-x", cat(&k1, &cat(&k2, &x))),
        ("near-c1-x-c2", cat(&k1, &cat(&x, &k2))),
    ]
}

fn gen_concat_sign_ext_by_slice(c: &mut Ctx) -> Variants {
    let (x, y, w) = (c.v(), c.v(), c.w);
    let mut v = vec![
        ("msb-y", cat(&bit(&y, w - 1), &y)),
        ("near-other-var", cat(&bit(&x, w - 1), &y)),
    ];
    if w >= 2 {
        v.push(("near-not-msb", cat(&bit(&y, w - 2), &y)));
    }
    v
}

fn gen_concat_sign_ext_by_sext_slice(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let e = c.rng.range(1, 3);
    let mut v = vec![("msb-sext", cat(&bit(&x, w - 1), &sext(&x, e)))];
    if w >= 2 {
        v.push(("near-not-msb", cat(&bit(&x, w - 2), &sext(&x, e))));
    }
    v
}

fn gen_concat_sign_ext_by_msb_term(c: &mut Ctx) -> Variants {
    let (z, b, d) = (c.v(), boolvar(), boolvar());
    let e = c.rng.range(1, 3);
    vec![
        ("b-cat(b,z)", cat(&b, &cat(&b, &z))),
        ("b-b", cat(&b, &b)),
        ("b-sext(cat(b,z))", cat(&b, &sext(&cat(&b, &z), e))),
        ("near-b-cat(z,b)", cat(&b, &cat(&z, &b))),
        ("near-b-cat(d,z)", cat(&b, &cat(&d, &z))),
    ]
}

fn gen_sext_zero_ext(c: &mut Ctx) -> Variants {
    let x = c.v();
    vec![("ext0", sext(&x, 0))]
}

fn gen_sext_bool_to_ite(c: &mut Ctx) -> Variants {
    let b = boolvar();
    vec![("bool", sext(&b, c.w))]
}

fn gen_sext_merge_nested(c: &mut Ctx) -> Variants {
    if c.w < 2 {
        return vec![];
    }
    let x = c.v();
    let (e1, e2) = (c.rng.range(1, 3), c.rng.range(1, 3));
    vec![("nested", sext(&sext(&x, e1), e2))]
}

fn gen_slice_whole_range(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let mut v = vec![("whole", sl(&x, 0, w - 1))];
    if w >= 2 {
        v.push(("near-drop-msb", sl(&x, 0, w - 2)));
        v.push(("near-drop-lsb", sl(&x, 1, w - 1)));
    }
    v
}

fn gen_slice_of_slice(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let l1 = c.rng.below(w);
    let h1 = c.rng.range(l1, w - 1);
    let iw = h1 - l1 + 1;
    let l2 = c.rng.below(iw);
    let h2 = c.rng.range(l2, iw - 1);
    vec![("nested", sl(&sl(&x, l1, h1), l2, h2))]
}

fn gen_slice_of_concat(c: &mut Ctx) -> Variants {
    let (hi, lo, w) = (c.v(), c.v(), c.w);
    let t = cat(&hi, &lo);
    let l = c.rng.below(w);
    let h = c.rng.range(l, w - 1);
    vec![
        ("in-lo", sl(&t, l, h)),
        ("in-hi", sl(&t, w + l, w + h)),
        ("straddle", sl(&t, l, w + h)),
        ("whole", sl(&t, 0, 2 * w - 1)),
    ]
}

fn gen_slice_of_sext(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let e = c.rng.range(1, 3);
    let t = sext(&x, e);
    let l = c.rng.below(w);
    let h = c.rng.range(l, w - 1);
    let le = c.rng.below(e);
    let he = c.rng.range(le, e - 1);
    vec![
        ("in-base", sl(&t, l, h)),
        ("in-ext", sl(&t, w + le, w + he)),
        ("straddle", sl(&t, l, w + he)),
        ("straddle-msb", sl(&t, l, w + e - 1)),
    ]
}

fn gen_slice_of_ite(c: &mut Ctx) -> Variants {
    let (x, y, b, w) = (c.v(), c.v(), boolvar(), c.w);
    let l = c.rng.below(w);
    let h = c.rng.range(l, w - 1);
    vec![("ite", sl(&ite(&b, &x, &y), l, h))]
}

fn gen_slice_of_bitwise_op(c: &mut Ctx) -> Variants {
    let (x, y, w) = (c.v(), c.v(), c.w);
    let l = c.rng.below(w);
    let h = c.rng.range(l, w - 1);
    vec![
        ("not", sl(&not(&x), l, h)),
        ("and", sl(&and(&x, &y), l, h)),
        ("or", sl(&or(&x, &y), l, h)),
        ("xor", sl(&xor(&x, &y), l, h)),
    ]
}

fn gen_slice_of_neg(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    let h = c.rng.below(w);
    let mut v = vec![("lsb-based", sl(&neg(&x), 0, h))];
    if w >= 2 {
        let l = c.rng.range(1, w - 1);
        let h = c.rng.range(l, w - 1);
        v.push(("near-l1", sl(&neg(&x), l, h)));
    }
    v
}

fn gen_slice_lsb_of_add(c: &mut Ctx) -> Variants {
    let (x, y, w) = (c.v(), c.v(), c.w);
    let t = add(&x, &y);
    let mut v = vec![("lsb", sl(&t, 0, 0))];
    if w >= 2 {
        v.push(("near-bit1", sl(&t, 1, 1)));
        v.push(("near-0-1", sl(&t, 0, 1)));
    }
    v
}

fn gen_slice_lsb_of_sll(c: &mut Ctx) -> Variants {
    let (x, y, w) = (c.v(), c.v(), c.w);
    let t = sll(&x, &y);
    let mut v = vec![("lsb", sl(&t, 0, 0))];
    if w >= 2 {
        v.push(("near-bit1", sl(&t, 1, 1)));
    }
    v
}

fn gen_add_by_zero(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    vec![
        ("zero-x", add(&bv_zero(w), &x)),
        ("x-zero", add(&x, &bv_zero(w))),
    ]
}

fn gen_neg_bool(c: &mut Ctx) -> Variants {
    let (b, x) = (boolvar(), c.v());
    let mut v = vec![("bool", neg(&b))];
    if c.w > 1 {
        v.push(("near-wide", neg(&x)));
    }
    v
}

fn gen_mul_by_zero(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    vec![
        ("zero-x", mul(&bv_zero(w), &x)),
        ("x-zero", mul(&x, &bv_zero(w))),
    ]
}

fn gen_mul_by_one(c: &mut Ctx) -> Variants {
    let (x, w) = (c.v(), c.w);
    vec![
        ("one-x", mul(&bv_one(w), &x)),
        ("x-one", mul(&x, &bv_one(w))),
    ]
}

fn gen_read_over_write_same_index(c: &mut Ctx) -> Variants {
    let (a, i, j) = c.arr();
    let v = c.v();
    vec![
        ("same-index", rd(&wr(&a, &i, &v), &i)),
        ("near-other-index", rd(&wr(&a, &i, &v), &j)),
    ]
}

fn gen_write_same_value(c: &mut Ctx) -> Variants {
    let (a, i, j) = c.arr();
    vec![
        ("same", wr(&a, &i, &rd(&a, &i))),
        ("near-other-index", wr(&a, &i, &rd(&a, &j))),
    ]
}

fn gen_write_conditional_same_value(c: &mut Ctx) -> Variants {
    let (a, i, j) = c.arr();
    let (v, b) = (c.v(), boolvar());
    vec![
        ("then-read", wr(&a, &i, &ite(&b, &rd(&a, &i), &v))),
        ("else-read", wr(&a, &i, &ite(&b, &v, &rd(&a, &i)))),
        ("near-other-index", wr(&a, &i, &ite(&b, &rd(&a, &j), &v))),
    ]
}

const TARGETED: &[(&str, Gen)] = &[
    ("NotBoolXorEqSwap", gen_not_bool_xor_eq_swap),
    ("NotIteConst", gen_not_ite_const),
    ("AndConstPropagation", gen_and_const_propagation),
    ("AndComplement", gen_and_complement),
    ("AndBoolMask", gen_and_bool_mask),
    ("AndMergeNestedAnds", gen_and_merge_nested_ands),
    ("AndDeMorganNotNot", gen_and_demorgan_not_not),
    ("AndAbsorbComplementInOr", gen_and_absorb_complement_in_or),
    ("AndDistributeOverOr", gen_and_distribute_over_or),
    (
        "AndMergeAdjacentEqSliceConsts",
        gen_and_merge_adjacent_eq_slice_consts,
    ),
    (
        "AndBitLevelEqReconstruction",
        gen_and_bit_level_eq_reconstruction,
    ),
    (
        "AndBitLevelMaskedEqReconstruction",
        gen_and_bit_level_masked_eq_reconstruction,
    ),
    ("OrConstPropagation", gen_or_const_propagation),
    ("OrComplement", gen_or_complement),
    ("OrMergeNestedOrs", gen_or_merge_nested_ors),
    ("OrDeMorganNotNot", gen_or_demorgan_not_not),
    ("OrAbsorbComplementInAnd", gen_or_absorb_complement_in_and),
    ("OrAbsorbIteCond", gen_or_absorb_ite_cond),
    ("OrMergeIteZeroBranches", gen_or_merge_ite_zero_branches),
    ("OrDistributeOverAnd", gen_or_distribute_over_and),
    (
        "OrMergeEqConstOneBitDiff",
        gen_or_merge_eq_const_one_bit_diff,
    ),
    (
        "OrMergeEqConstOneBitDiffAssoc",
        gen_or_merge_eq_const_one_bit_diff_assoc,
    ),
    (
        "OrBitLevelClauseReconstruction",
        gen_or_bit_level_clause_reconstruction,
    ),
    (
        "OrBitLevelMaskedClauseReconstruction",
        gen_or_bit_level_masked_clause_reconstruction,
    ),
    ("XorConstPropagation", gen_xor_const_propagation),
    ("XorSelf", gen_xor_self),
    ("XorComplement", gen_xor_complement),
    ("EqBoolViaXor", gen_eq_bool_via_xor),
    ("EqRefl", gen_eq_refl),
    ("EqComplement", gen_eq_complement),
    ("EqBoolMaskConst", gen_eq_bool_mask_const),
    ("EqNotConst", gen_eq_not_const),
    ("EqXorZero", gen_eq_xor_zero),
    ("EqAndConst", gen_eq_and_const),
    ("UltConstX", gen_ult_const_x),
    ("UltConstY", gen_ult_const_y),
    ("UltConcatConst", gen_ult_concat_const),
    ("SltRefl", gen_slt_refl),
    ("SltConstX", gen_slt_const_x),
    ("SltConstY", gen_slt_const_y),
    ("SltNonnegativeBound", gen_slt_nonnegative_bound),
    ("IteConstCond", gen_ite_const_cond),
    ("IteSameBranches", gen_ite_same_branches),
    ("IteNotCondSwap", gen_ite_not_cond_swap),
    ("IteNotBranches", gen_ite_not_branches),
    (
        "IteBoolComplementBranches",
        gen_ite_bool_complement_branches,
    ),
    ("IteBoolBranchConst", gen_ite_bool_branch_const),
    ("IteSameCondNested", gen_ite_same_cond_nested),
    ("IteNestedSharedBranch", gen_ite_nested_shared_branch),
    ("IteWriteBranches", gen_ite_write_branches),
    ("ConcatConst", gen_concat_const),
    ("ConcatAssocConstPrefix", gen_concat_assoc_const_prefix),
    ("ConcatSignExtBySlice", gen_concat_sign_ext_by_slice),
    (
        "ConcatSignExtBySextSlice",
        gen_concat_sign_ext_by_sext_slice,
    ),
    ("ConcatSignExtByMsbTerm", gen_concat_sign_ext_by_msb_term),
    ("SextZeroExt", gen_sext_zero_ext),
    ("SextBoolToIte", gen_sext_bool_to_ite),
    ("SextMergeNested", gen_sext_merge_nested),
    ("SliceWholeRange", gen_slice_whole_range),
    ("SliceOfSlice", gen_slice_of_slice),
    ("SliceOfConcat", gen_slice_of_concat),
    ("SliceOfSext", gen_slice_of_sext),
    ("SliceOfIte", gen_slice_of_ite),
    ("SliceOfBitwiseOp", gen_slice_of_bitwise_op),
    ("SliceOfNeg", gen_slice_of_neg),
    ("SliceLsbOfAdd", gen_slice_lsb_of_add),
    ("SliceLsbOfSll", gen_slice_lsb_of_sll),
    ("AddByZero", gen_add_by_zero),
    ("NegBool", gen_neg_bool),
    ("MulByZero", gen_mul_by_zero),
    ("MulByOne", gen_mul_by_one),
    ("ReadOverWriteSameIndex", gen_read_over_write_same_index),
    ("WriteSameValue", gen_write_same_value),
    (
        "WriteConditionalSameValue",
        gen_write_conditional_same_value,
    ),
];

// ------------------------------------------------------------------------------------------------
// All-constant-operand mode: exercises `FolOp::simplify`'s constant folding (`eval_const_op`,
// through the simulator) for every op. The oracle here is the bit-level simulation of
// `bitblast(orig)`, which does not go through the word-level simulator.
// ------------------------------------------------------------------------------------------------

/// Rebuild `t` with `map` substituted, using raw nodes (no folding during construction).
fn raw_subst(t: &Term, map: &GHashMap<Term, Term>, memo: &mut GHashMap<Term, Term>) -> Term {
    if let Some(r) = map.get(t) {
        return r.clone();
    }
    if let Some(r) = memo.get(t) {
        return r.clone();
    }
    let r = match &**t {
        TermType::Op(o) => {
            let ch: Vec<Term> = o.terms.iter().map(|s| raw_subst(s, map, memo)).collect();
            raw(o.op, ch)
        }
        _ => t.clone(),
    };
    memo.insert(t.clone(), r.clone());
    r
}

fn const_pool(rng: &mut Rng, w: usize) -> Vec<(&'static str, BitVec)> {
    let mut p = vec![
        ("zero", BitVec::zero(w)),
        ("one", BitVec::one(w)),
        ("ones", BitVec::ones(w)),
        ("min", bv_bit(w, w - 1)),
        ("rand", rng.bits(w)),
    ];
    if w > 64 {
        // a shift amount / divisor with a set bit at index >= 64
        let mut hi = rng.bits(w);
        hi.set(64, true);
        p.push(("bit64", hi));
    }
    if w > 1 {
        let mut small = BitVec::zero(w);
        small.set(0, true);
        small.set(1, rng.chance(1, 2));
        p.push(("small", small));
    }
    p
}

fn const_cases(rng: &mut Rng, w: usize, out: &mut Vec<Case>) {
    let pool = const_pool(rng, w);
    let pick = |rng: &mut Rng, pool: &[(&'static str, BitVec)]| -> (String, Term) {
        let (n, c) = &pool[rng.below(pool.len())];
        (n.to_string(), Term::bv_const(c.clone()))
    };
    let mut push = |name: String, t: Term| {
        out.push(Case {
            name: format!("const/w{w}/{name}"),
            orig: t,
        })
    };

    const BIN: [FolOp; 18] = [
        And, Or, Xor, Sll, Srl, Sra, Rol, Ror, Add, Mul, Udiv, Urem, Sdiv, Srem, Smod, Eq, Ult, Slt,
    ];
    for op in BIN {
        // always: a random lhs against every pool constant (covers zero divisors / huge shifts);
        // above 64 bits the all-constant bit-blast of a divider/multiplier is expensive, keep the
        // boundary-relevant constants only
        let (an, a) = pick(rng, &pool);
        let expensive = w > 64 && matches!(op, Mul | Udiv | Urem | Sdiv | Srem | Smod);
        for (bn, b) in &pool {
            if expensive && !matches!(*bn, "zero" | "bit64" | "rand") {
                continue;
            }
            push(
                format!("{op}/{an}-{bn}"),
                r2(op, &a, &Term::bv_const(b.clone())),
            );
        }
        let (cn, c) = pick(rng, &pool);
        push(format!("{op}/{cn}-{cn}"), r2(op, &c, &c));
    }
    for op in [Not, Neg, Redxor] {
        for (n, c) in &pool {
            push(format!("{op}/{n}"), r1(op, &Term::bv_const(c.clone())));
        }
    }
    let (an, a) = pick(rng, &pool);
    let (bn, b) = pick(rng, &pool);
    push(
        format!("Ite/1-{an}-{bn}"),
        ite(&Term::bool_const(true), &a, &b),
    );
    push(
        format!("Ite/0-{an}-{bn}"),
        ite(&Term::bool_const(false), &a, &b),
    );
    let w2 = rng.range(1, w);
    let c2 = Term::bv_const(rng.bits(w2));
    push(format!("Concat/{an}-rand{w2}"), cat(&a, &c2));
    push(format!("Concat/rand{w2}-{an}"), cat(&c2, &a));
    let e = rng.range(1, 3);
    push(format!("Sext/{an}-{e}"), sext(&a, e));
    push(format!("Sext/{bn}-0"), sext(&b, 0));
    let l = rng.below(w);
    let h = rng.range(l, w - 1);
    push(format!("Slice/{an}-{l}-{h}"), sl(&a, l, h));
    push(format!("Slice/{bn}-whole"), sl(&b, 0, w - 1));

    // non-core ops: normalize over variables, then substitute constants into a raw copy
    const NONCORE2: [FolOp; 15] = [
        Sub, Nand, Nor, Xnor, Neq, Ugt, Ulte, Ugte, Sgt, Slte, Sgte, Iff, Implies, Udivo, Uext,
    ];
    let (x, y) = (var(w), var(w));
    for op in NONCORE2 {
        let (an, a) = pick(rng, &pool);
        let (bn, b) = pick(rng, &pool);
        let (shape, a, b) = if op == Uext {
            (Term::new_op(op, [x.clone(), dummy(rng.range(1, 3))]), a, b)
        } else if op == Implies {
            let (p, q) = (var(1), var(1));
            let (a, b) = (
                Term::bool_const(rng.chance(1, 2)),
                Term::bool_const(rng.chance(1, 2)),
            );
            let shape = Term::new_op(op, [p.clone(), q.clone()]);
            let mut m = GHashMap::new();
            m.insert(p, a);
            m.insert(q, b);
            push(
                format!("{op}/bool"),
                raw_subst(&shape, &m, &mut GHashMap::new()),
            );
            continue;
        } else {
            (Term::new_op(op, [x.clone(), y.clone()]), a, b)
        };
        let mut map = GHashMap::new();
        map.insert(x.clone(), a);
        map.insert(y.clone(), b);
        push(
            format!("{op}/{an}-{bn}"),
            raw_subst(&shape, &map, &mut GHashMap::new()),
        );
    }
    for op in [Inc, Dec, Redand, Redor] {
        let (an, a) = pick(rng, &pool);
        let shape = Term::new_op(op, [x.clone()]);
        let mut map = GHashMap::new();
        map.insert(x.clone(), a);
        push(
            format!("{op}/{an}"),
            raw_subst(&shape, &map, &mut GHashMap::new()),
        );
    }
}

// ------------------------------------------------------------------------------------------------
// The oracle
// ------------------------------------------------------------------------------------------------

#[derive(Default)]
struct Stats {
    cases: usize,
    assignments: usize,
    bb_cases: usize,
    const_cases: usize,
    const_folded: usize,
    /// cases where neither oracle could run (simulator panicked, bit-blast over budget)
    unchecked: Vec<String>,
}

fn simulate_bits(tv: &TermVec, val: &mut GHashMap<Term, Value>) -> Vec<Lbool> {
    tv.iter()
        .map(|t| t.simulate(val).into_bv().unwrap().get(0))
        .collect()
}

fn check_case(
    case: &Case,
    cfg: &Cfg,
    rng: &mut Rng,
    cov: &mut BTreeMap<&'static str, usize>,
    stats: &mut Stats,
    all_const: bool,
) -> Vec<Finding> {
    stats.cases += 1;
    let orig = &case.orig;
    let vars = free_vars(orig);
    let mut findings = Vec::new();
    let mk = |kind,
              level,
              simp: Option<Term>,
              fired: Vec<&'static str>,
              assignment: String,
              detail: String| Finding {
        kind,
        case: case.name.clone(),
        level,
        orig: orig.clone(),
        simp,
        fired,
        assignment,
        detail,
    };

    // 1. simplify at every level
    struct Simp {
        term: Term,
        levels: Vec<OptLevel>,
        fired: Vec<&'static str>,
    }
    let mut simps: Vec<Simp> = Vec::new();
    for &lv in LEVELS {
        audit::reset();
        let r = guarded(|| orig.simplify_with_ctx(&SimplifyCtx::new(lv), &mut GHashMap::new()));
        let fired = audit::fired();
        for f in &fired {
            *cov.entry(f).or_insert(0) += 1;
        }
        match r {
            Err(msg) => findings.push(mk(Kind::SimplifyPanic, lv, None, fired, String::new(), msg)),
            Ok(t) => {
                if let Some(s) = simps.iter_mut().find(|s| s.term == t) {
                    s.levels.push(lv);
                } else {
                    simps.push(Simp {
                        term: t,
                        levels: vec![lv],
                        fired,
                    });
                }
            }
        }
    }
    if all_const {
        stats.const_cases += 1;
        if simps.iter().any(|s| s.term.is_const()) {
            stats.const_folded += 1;
        }
    }
    let changed: Vec<&Simp> = simps.iter().filter(|s| s.term != *orig).collect();
    let agreement_only = changed.is_empty();
    if agreement_only && !all_const && !rng.chance(1, 6) {
        // nothing was rewritten; the bit-blast/simulator agreement check runs on a sample only
        return findings;
    }

    // 2. assignments
    let bits: usize = vars.iter().map(|v| sort_bits(v.sort())).sum();
    let exhaustive = bits <= cfg.exh_bits;
    let n = if all_const {
        1
    } else if exhaustive {
        1usize << bits
    } else {
        cfg.samples
    };
    let assigns: Vec<Assignment> = (0..n)
        .map(|i| {
            if exhaustive {
                exhaustive_assignment(&vars, i as u64)
            } else {
                random_assignment(rng, &vars)
            }
        })
        .collect();

    // 3. word-level simulator oracle (not for all-constant terms: same code as the fold)
    let mut sim_ok = !all_const;
    let mut orig_vals: Vec<Value> = Vec::new();
    if sim_ok {
        let mut bad: Vec<bool> = vec![false; changed.len()];
        for a in &assigns {
            let mut val: GHashMap<Term, Value> = a.iter().cloned().collect();
            let vo = match guarded(|| orig.simulate(&mut val)) {
                Ok(v) => v,
                Err(m) => {
                    findings.push(mk(
                        Kind::OraclePanic,
                        OptLevel::O0,
                        None,
                        vec![],
                        show_assignment(a),
                        format!("simulate(orig): {m}"),
                    ));
                    sim_ok = false;
                    break;
                }
            };
            stats.assignments += 1;
            for (k, s) in changed.iter().enumerate() {
                if bad[k] {
                    continue;
                }
                match guarded(|| s.term.simulate(&mut val)) {
                    Err(m) => {
                        bad[k] = true;
                        findings.push(mk(
                            Kind::OraclePanic,
                            s.levels[0],
                            Some(s.term.clone()),
                            s.fired.clone(),
                            show_assignment(a),
                            format!("simulate(simp): {m}"),
                        ));
                    }
                    Ok(vs) => {
                        if let Some(d) = cmp_value(&vo, &vs) {
                            bad[k] = true;
                            findings.push(mk(
                                Kind::RewriteMismatch,
                                s.levels[0],
                                Some(s.term.clone()),
                                s.fired.clone(),
                                show_assignment(a),
                                format!("simulate(orig) != simulate(simp) at levels {:?}: {d}; orig={} simp={}", s.levels, show_value(&vo), show_value(&vs)),
                            ));
                        }
                    }
                }
            }
            orig_vals.push(vo);
        }
    }

    // 4. bit-level oracle
    let cost = bitblast_cost(orig)
        + changed
            .iter()
            .map(|s| bitblast_cost(&s.term))
            .sum::<usize>();
    // all-constant terms fold gate by gate during bit-blasting (0.5 s for a 140-bit divider in
    // debug), so the bit-level oracle always runs for them
    let budget = if all_const {
        usize::MAX
    } else if !sim_ok {
        cfg.bb_budget * 10
    } else {
        cfg.bb_budget
    };
    if cost > budget {
        if !sim_ok {
            stats
                .unchecked
                .push(format!("{} (bit-blast cost {cost})", case.name));
        }
        return findings;
    }
    let mut bb: GHashMap<Term, TermVec> = GHashMap::new();
    let bo = match guarded(|| orig.bitblast(&mut bb)) {
        Ok(b) => b,
        Err(m) => {
            findings.push(mk(
                Kind::OraclePanic,
                OptLevel::O0,
                None,
                vec![],
                String::new(),
                format!("bitblast(orig): {m}"),
            ));
            return findings;
        }
    };
    let mut bs: Vec<Option<TermVec>> = Vec::new();
    for s in &changed {
        match guarded(|| s.term.bitblast(&mut bb)) {
            Ok(b) => bs.push(Some(b)),
            Err(m) => {
                bs.push(None);
                findings.push(mk(
                    Kind::OraclePanic,
                    s.levels[0],
                    Some(s.term.clone()),
                    s.fired.clone(),
                    String::new(),
                    format!("bitblast(simp): {m}"),
                ));
            }
        }
    }
    stats.bb_cases += 1;
    let nb = if all_const {
        1
    } else {
        cfg.bb_samples.min(assigns.len())
    };
    let mut bad: Vec<bool> = vec![false; changed.len()];
    let mut agree_bad = false;
    for (k, a) in assigns.iter().take(nb).enumerate() {
        let mut bval: GHashMap<Term, Value> = GHashMap::new();
        for (v, val) in a {
            let Some(bits) = bb.get(v) else { continue };
            for (bt, l) in bits.iter().zip(value_bits(val, v.sort())) {
                bval.insert(bt.clone(), Value::Bv(LboolVec::from_elem(l, 1)));
            }
        }
        let ob = match guarded(|| simulate_bits(&bo, &mut bval)) {
            Ok(b) => b,
            Err(m) => {
                findings.push(mk(
                    Kind::OraclePanic,
                    OptLevel::O0,
                    None,
                    vec![],
                    show_assignment(a),
                    format!("simulate(bitblast(orig)): {m}"),
                ));
                return findings;
            }
        };
        if !agree_bad
            && let Some(vo) = orig_vals.get(k)
            && let Some(d) = cmp_bits(&value_bits(vo, orig.sort()), &ob)
        {
            agree_bad = true;
            findings.push(mk(
                Kind::BitblastSimMismatch,
                OptLevel::O0,
                None,
                vec![],
                show_assignment(a),
                format!("simulate(orig) != simulate(bitblast(orig)): {d}"),
            ));
        }
        for (i, s) in changed.iter().enumerate() {
            if bad[i] {
                continue;
            }
            let Some(sb) = &bs[i] else { continue };
            let got = match guarded(|| simulate_bits(sb, &mut bval)) {
                Ok(b) => b,
                Err(m) => {
                    bad[i] = true;
                    findings.push(mk(
                        Kind::OraclePanic,
                        s.levels[0],
                        Some(s.term.clone()),
                        s.fired.clone(),
                        show_assignment(a),
                        format!("simulate(bitblast(simp)): {m}"),
                    ));
                    continue;
                }
            };
            if let Some(d) = cmp_bits(&ob, &got) {
                bad[i] = true;
                let kind = if sim_ok {
                    Kind::BitblastRewriteMismatch
                } else {
                    Kind::RewriteMismatch
                };
                let exp: Vec<String> = ob.iter().rev().map(|l| l.to_string()).collect();
                let gotv: Vec<String> = got.iter().rev().map(|l| l.to_string()).collect();
                findings.push(mk(
                    kind,
                    s.levels[0],
                    Some(s.term.clone()),
                    s.fired.clone(),
                    show_assignment(a),
                    format!(
                        "bitblast(orig) != bitblast(simp) at levels {:?}: {d}; orig={} simp={}",
                        s.levels,
                        exp.join(""),
                        gotv.join("")
                    ),
                ));
            }
        }
    }
    findings
}

/// Replace a finding by the same kind of finding on its smallest failing sub-term, if any.
fn shrink(f: &Finding, cfg: &Cfg, rng: &mut Rng) -> Finding {
    let small = Cfg {
        samples: cfg.samples.min(64),
        bb_samples: 8,
        ..cfg.clone()
    };
    let all_const = f.case.starts_with("const/");
    for sub in sub_ops(&f.orig) {
        let case = Case {
            name: format!("{}/sub{}", f.case, node_count(&sub)),
            orig: sub,
        };
        let mut cov = BTreeMap::new();
        let mut st = Stats::default();
        let fs = check_case(&case, &small, rng, &mut cov, &mut st, all_const);
        if let Some(g) = fs.into_iter().find(|g| g.kind == f.kind) {
            return g;
        }
    }
    f.clone()
}

fn gc_if_large() {
    if term_mgr().len() > 200_000 {
        term_gc();
    }
}

fn out_dir() -> std::path::PathBuf {
    let d = match std::env::var("LOGICRS_AUDIT_OUT") {
        Ok(p) => std::path::PathBuf::from(p),
        Err(_) => std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("target")
            .join("rewrite_audit"),
    };
    std::fs::create_dir_all(&d).unwrap();
    d
}

#[test]
fn rewrite_audit() {
    // the bit-level simulator recurses over the bit DAG (depth ~ w^2 for a w-bit divider),
    // which overflows the default 2 MiB test-thread stack at w >= 64
    let h = std::thread::Builder::new()
        .name("rewrite_audit".into())
        .stack_size(1 << 30)
        .spawn(audit_main)
        .unwrap();
    if let Err(e) = h.join() {
        std::panic::resume_unwind(e);
    }
}

fn progress(t0: &Instant, msg: &str) {
    if std::env::var("LOGICRS_AUDIT_QUIET").is_err() {
        eprintln!("[{:7.1}s] {msg}", t0.elapsed().as_secs_f64());
    }
}

fn audit_main() {
    install_panic_hook();
    let cfg = Cfg::from_env();
    let t0 = Instant::now();
    let mut rng = Rng::new(cfg.seed);
    let mut cov: BTreeMap<&'static str, usize> = RULES.iter().map(|r| (*r, 0)).collect();
    let mut stats = Stats::default();
    let mut findings: Vec<Finding> = Vec::new();
    let widths: Vec<usize> = EXHAUSTIVE_WIDTHS
        .iter()
        .chain(RANDOM_WIDTHS)
        .copied()
        .collect();
    let mut gen_panics: Vec<String> = Vec::new();

    // (i) targeted shapes, every rule, every width
    for (rule, g) in TARGETED {
        progress(&t0, &format!("targeted {rule}"));
        for &w in &widths {
            let variants = {
                let mut ctx = Ctx { rng: &mut rng, w };
                guarded(|| g(&mut ctx))
            };
            match variants {
                Err(m) => gen_panics.push(format!("{rule}/w{w}: construction panicked: {m}")),
                Ok(vs) => {
                    for (tag, orig) in vs {
                        let case = Case {
                            name: format!("{rule}/w{w}/{tag}"),
                            orig,
                        };
                        findings.extend(check_case(
                            &case, &cfg, &mut rng, &mut cov, &mut stats, false,
                        ));
                    }
                }
            }
        }
        gc_if_large();
    }
    let t_targeted = t0.elapsed();

    // (ii) all-constant operands, every op, every width
    for &w in &widths {
        progress(&t0, &format!("const w{w}"));
        let mut cases = Vec::new();
        match guarded(|| const_cases(&mut rng, w, &mut cases)) {
            Err(m) => gen_panics.push(format!("const/w{w}: construction panicked: {m}")),
            Ok(()) => {}
        }
        for case in &cases {
            findings.extend(check_case(case, &cfg, &mut rng, &mut cov, &mut stats, true));
        }
        gc_if_large();
    }
    let t_const = t0.elapsed() - t_targeted;

    // (iii) generic random terms over all ops
    for &w in &widths {
        progress(&t0, &format!("generic w{w}"));
        // above 64 bits the word-level simulator is unusable (see the oracle-limitation class) and
        // the bit-level oracle is costly: half the budget there
        let count = if w > 64 {
            cfg.generic_per_width / 2
        } else {
            cfg.generic_per_width
        };
        for k in 0..count {
            let case = match guarded(|| generic_case(&mut rng, w, k)) {
                Ok(c) => c,
                Err(m) => {
                    gen_panics.push(format!("generic/w{w}/{k}: construction panicked: {m}"));
                    continue;
                }
            };
            findings.extend(check_case(
                &case, &cfg, &mut rng, &mut cov, &mut stats, false,
            ));
            if k % 4 == 0 {
                let case = generic_array_case(&mut rng, w, k);
                findings.extend(check_case(
                    &case, &cfg, &mut rng, &mut cov, &mut stats, false,
                ));
            }
            if k % 32 == 31 {
                gc_if_large();
            }
        }
    }
    let t_generic = t0.elapsed() - t_targeted - t_const;

    progress(&t0, &format!("grouping {} findings", findings.len()));
    // ---- group findings: one representative (smallest) per (kind, class, rules/message) ----
    fn class_of(f: &Finding) -> &'static str {
        match f.kind {
            Kind::OraclePanic => "oracle-limitation",
            Kind::BitblastSimMismatch => "bitblast-vs-simulator",
            // a simplify panic raised inside the simulator / LboolVec is the constant folder
            // (`eval_const_op`), whatever rules fired before it exposed the constant operands
            _ if f.fired.is_empty()
                || f.detail.contains("simulate.rs")
                || f.detail.contains("lbool.rs") =>
            {
                "const-fold"
            }
            _ => "rule",
        }
    }
    fn key_of(f: &Finding) -> String {
        let what = match f.kind {
            // strip the location suffix so the same assertion groups together
            Kind::SimplifyPanic | Kind::OraclePanic => {
                f.detail.split(" (").next().unwrap_or("").to_string()
            }
            _ => String::new(),
        };
        let top = match &*f.orig {
            TermType::Op(o) => format!("{}", o.op),
            _ => "leaf".into(),
        };
        let rules = if f.fired.is_empty() {
            top
        } else {
            let mut r = f.fired.clone();
            r.sort();
            r.dedup();
            r.join("+")
        };
        format!("{}|{:?}|{}|{}", class_of(f), f.kind, rules, what)
    }
    fn group(findings: Vec<Finding>) -> BTreeMap<String, (Finding, usize)> {
        let mut groups: BTreeMap<String, (Finding, usize)> = BTreeMap::new();
        for f in findings {
            let k = key_of(&f);
            match groups.get_mut(&k) {
                Some((rep, n)) => {
                    *n += 1;
                    if f.size() < rep.size() {
                        *rep = f;
                    }
                }
                None => {
                    groups.insert(k, (f, 1));
                }
            }
        }
        groups
    }
    // shrink each representative to its smallest failing sub-term, then regroup (the minimal
    // term may belong to a different class, e.g. a const-fold panic under a rule result)
    let mut shrunk = Vec::new();
    for (_, (rep, count)) in group(findings.clone()) {
        let s = shrink(&rep, &cfg, &mut rng);
        shrunk.extend(std::iter::repeat_n(s, count));
    }
    let groups = group(shrunk);

    // export reproducers and render, by class (stale reproducers of an earlier run are removed)
    let dir = out_dir();
    for e in std::fs::read_dir(&dir).unwrap().flatten() {
        let p = e.path();
        if p.extension().is_some_and(|x| x == "btor")
            && p.file_stem()
                .is_some_and(|n| n.to_string_lossy().chars().all(|c| c.is_ascii_digit()))
        {
            let _ = std::fs::remove_file(p);
        }
    }
    let mut report = String::new();
    let mut per_class: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut n = 0;
    for class in [
        "rule",
        "const-fold",
        "bitblast-vs-simulator",
        "oracle-limitation",
    ] {
        let mine: Vec<_> = groups
            .iter()
            .filter(|(_, (f, _))| class_of(f) == class)
            .collect();
        if mine.is_empty() {
            continue;
        }
        per_class.insert(class, mine.len());
        let _ = writeln!(report, "---- class {class}: {} group(s) ----", mine.len());
        for (key, (small, count)) in mine {
            n += 1;
            let header = format!(
                "rewrite audit finding #{n} [{key}]\ncase={} level={:?} fired={:?}\ninput: {}\n{}",
                small.case, small.level, small.fired, small.assignment, small.detail
            );
            let vars = free_vars(&small.orig);
            let path = dir.join(format!("{n}.btor"));
            let text = match &small.simp {
                Some(s) => btor2::neq_bad_model(&small.orig, s, &header, &vars),
                None => {
                    let mut w = btor2::Btor2Writer::new();
                    w.comment(&header);
                    w.comment("no simplified term (panic); DAG of orig only, no bad property");
                    for (k, v) in vars.iter().enumerate() {
                        w.symbol(v, format!("x{k}"));
                    }
                    w.node(&small.orig);
                    w.finish()
                }
            };
            std::fs::write(&path, text).unwrap();
            let _ = writeln!(
                report,
                "{}  ({count} occurrence(s) in this run)",
                small.render(n, Some(&path.display().to_string()))
            );
        }
    }
    let failing_groups: usize = ["rule", "const-fold", "bitblast-vs-simulator"]
        .iter()
        .map(|c| per_class.get(c).copied().unwrap_or(0))
        .sum();
    let oracle_groups = per_class.get("oracle-limitation").copied().unwrap_or(0);

    // ---- coverage table ----
    let mut table = String::new();
    let _ = writeln!(table, "{:<40} {:>8}", "rule", "hits");
    for r in RULES {
        let _ = writeln!(table, "{:<40} {:>8}", r, cov.get(r).copied().unwrap_or(0));
    }
    let _ = writeln!(
        table,
        "{:<40} {:>8}  (class const-fold: all-constant cases folded to a constant / cases)",
        "const-fold",
        format!("{}/{}", stats.const_folded, stats.const_cases)
    );
    let unknown: Vec<&&str> = cov.keys().filter(|k| !RULES.contains(k)).collect();
    let missing: Vec<&&str> = RULES
        .iter()
        .filter(|r| {
            cov.get(*r).copied().unwrap_or(0) == 0
                && !KNOWN_UNREACHABLE.iter().any(|(n, _)| n == *r)
        })
        .collect();
    let stale: Vec<&&str> = RULES
        .iter()
        .filter(|r| {
            cov.get(*r).copied().unwrap_or(0) > 0 && KNOWN_UNREACHABLE.iter().any(|(n, _)| n == *r)
        })
        .collect();

    let summary = format!(
        "cases={} (const={}, bit-level checked={}) assignments={} seed={} samples={} exh_bits={} generic/width={} widths={:?}\n\
         time: targeted {:.1?}, const {:.1?}, generic {:.1?}, total {:.1?}\n\
         findings: {} raw, {} distinct groups ({} failing: rule/const-fold/bitblast-vs-simulator; {} oracle limitations); unchecked cases: {}; generator panics: {}",
        stats.cases,
        stats.const_cases,
        stats.bb_cases,
        stats.assignments,
        cfg.seed,
        cfg.samples,
        cfg.exh_bits,
        cfg.generic_per_width,
        widths,
        t_targeted,
        t_const,
        t_generic,
        t0.elapsed(),
        findings.len(),
        groups.len(),
        failing_groups,
        oracle_groups,
        stats.unchecked.len(),
        gen_panics.len()
    );
    let mut full = String::new();
    let _ = writeln!(
        full,
        "== rewrite audit ==\n{summary}\n\n== coverage ==\n{table}"
    );
    if !unknown.is_empty() {
        let _ = writeln!(
            full,
            "rules fired but not in RULES (update the list): {unknown:?}"
        );
    }
    if !missing.is_empty() {
        let _ = writeln!(
            full,
            "rules with 0 hits (not in KNOWN_UNREACHABLE): {missing:?}"
        );
    }
    if !stale.is_empty() {
        let _ = writeln!(full, "rules in KNOWN_UNREACHABLE that fired: {stale:?}");
    }
    for (r, why) in KNOWN_UNREACHABLE {
        let _ = writeln!(full, "known unreachable: {r}: {why}");
    }
    if !stats.unchecked.is_empty() {
        let _ = writeln!(
            full,
            "\n== unchecked cases (warning: simulator panicked and bit-blast over budget) =="
        );
        for u in stats.unchecked.iter().take(40) {
            let _ = writeln!(full, "  {u}");
        }
        if stats.unchecked.len() > 40 {
            let _ = writeln!(full, "  ... {} more", stats.unchecked.len() - 40);
        }
    }
    if !gen_panics.is_empty() {
        let _ = writeln!(full, "\n== generator panics ==");
        for g in &gen_panics {
            let _ = writeln!(full, "  {g}");
        }
    }
    if !report.is_empty() {
        let _ = writeln!(
            full,
            "\n== findings (minimal representative per group; reproducers in {}) ==\n{report}",
            dir.display()
        );
    }
    println!("{full}");
    std::fs::write(dir.join("report.txt"), &full).unwrap();

    let mut problems = Vec::new();
    if failing_groups > 0 {
        problems.push(format!(
            "{failing_groups} failing finding group(s): {per_class:?}"
        ));
    }
    if !missing.is_empty() {
        problems.push(format!(
            "{} rule(s) with 0 hits: {missing:?}",
            missing.len()
        ));
    }
    if !stale.is_empty() {
        problems.push(format!("stale KNOWN_UNREACHABLE entries: {stale:?}"));
    }
    if !unknown.is_empty() {
        problems.push(format!("unknown rule names fired: {unknown:?}"));
    }
    if !gen_panics.is_empty() {
        problems.push(format!("{} generator panic(s)", gen_panics.len()));
    }
    assert!(
        problems.is_empty(),
        "rewrite audit failed: {}\nsee {}",
        problems.join("; "),
        dir.join("report.txt").display()
    );
}

/// `RULES` must list exactly the `impl RewriteRule for <Name>` blocks of simplify.rs, in order,
/// and every rule must have a targeted generator.
#[test]
fn rule_list_in_sync() {
    let src = include_str!("../src/fol/simplify.rs");
    let in_src: Vec<&str> = src
        .lines()
        .filter_map(|l| l.trim().strip_prefix("impl RewriteRule for "))
        .map(|r| r.trim_end_matches('{').trim())
        .filter(|n| *n != "RewritePipeline")
        .collect();
    assert_eq!(
        in_src, RULES,
        "RULES is out of sync with src/fol/simplify.rs"
    );
    let targeted: Vec<&str> = TARGETED.iter().map(|(n, _)| *n).collect();
    assert_eq!(
        targeted, RULES,
        "TARGETED generators are out of sync with RULES"
    );
    for (n, _) in KNOWN_UNREACHABLE {
        assert!(
            RULES.contains(n),
            "KNOWN_UNREACHABLE names an unknown rule {n}"
        );
    }
}

/// The BTOR2 writer produces a model that `catbtor` accepts (skipped when the binary is absent).
#[test]
fn btor2_writer_smoke() {
    let x = var(4);
    let y = var(4);
    let a = Term::new_var(Sort::Array(2, 4));
    let orig = sl(&sext(&add(&x, &rd(&a, &sl(&y, 0, 1))), 2), 1, 5);
    let simp = orig.simplify_with_ctx(&SimplifyCtx::new(OptLevel::O3), &mut GHashMap::new());
    let text = btor2::neq_bad_model(&orig, &simp, "smoke", &[x, y, a]);
    let path = out_dir().join("smoke.btor");
    std::fs::write(&path, &text).unwrap();
    let catbtor = std::env::var("CATBTOR").unwrap_or_else(|_| "catbtor".into());
    let on_path = || {
        std::env::var_os("PATH")
            .is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(&catbtor).is_file()))
    };
    if !std::path::Path::new(&catbtor).exists() && !on_path() {
        eprintln!(
            "catbtor not found at {catbtor}; wrote {} only",
            path.display()
        );
        return;
    }
    let out = std::process::Command::new(&catbtor)
        .arg(&path)
        .current_dir(out_dir())
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "catbtor rejected the model:\n{}\n{}",
        String::from_utf8_lossy(&out.stderr),
        text
    );
}

/// Cost probe: all-constant bit-blast of one wide divider (`cargo test -- --ignored bench_`).
#[test]
#[ignore]
fn bench_const_divider_bitblast() {
    for w in [64usize, 129, 140] {
        let a = Term::bv_const(BitVec::ones(w));
        let mut b = BitVec::zero(w);
        b.set(w - 1, true);
        b.set(3, true);
        let t = r2(Udiv, &a, &Term::bv_const(b));
        let t0 = Instant::now();
        let bb = t.bitblast(&mut GHashMap::new());
        let all_const = bb.iter().all(|b| b.is_const());
        eprintln!(
            "w={w}: bitblast {:?}, {} bits, all const: {all_const}, terms in manager: {}",
            t0.elapsed(),
            bb.len(),
            term_mgr().len()
        );
    }
}
