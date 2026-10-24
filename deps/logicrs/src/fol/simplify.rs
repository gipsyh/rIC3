use super::Term;
use crate::OptLevel;
use crate::fol::TermResult;
use crate::fol::Value;
use crate::fol::op::*;
use giputils::bitvec::BitVec;
use giputils::hash::GHashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SimplifyCtx {
    pub level: OptLevel,
}

impl Default for SimplifyCtx {
    #[inline]
    fn default() -> Self {
        Self {
            level: OptLevel::default(),
        }
    }
}

impl SimplifyCtx {
    #[inline]
    pub const fn new(level: OptLevel) -> Self {
        Self { level }
    }
}

trait RewriteRule {
    #[inline]
    fn opt_level(&self) -> OptLevel {
        OptLevel::O0
    }

    fn name(&self) -> &'static str {
        std::any::type_name::<Self>().rsplit("::").next().unwrap()
    }

    fn apply(&self, terms: &[Term]) -> TermResult;
}

/// Rule tracing and selective disabling, used by the rewrite-rule audit harness.
///
/// `LOGICRS_DISABLE_RULES=Name,Name` skips the named rules; `LOGICRS_TRACE_RULES=1` prints every
/// rule hit to stderr. `audit::fired()` returns the names of the rules that fired on the current
/// thread since the last `audit::reset()`, so a test can measure which rules a term exercised.
pub mod audit {
    use std::cell::RefCell;
    use std::collections::HashSet;
    use std::sync::OnceLock;

    thread_local! {
        static FIRED: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
        static DISABLED: RefCell<Option<HashSet<String>>> = const { RefCell::new(None) };
    }

    struct Env {
        disabled: HashSet<String>,
        trace: bool,
    }

    fn env() -> &'static Env {
        static E: OnceLock<Env> = OnceLock::new();
        E.get_or_init(|| Env {
            disabled: std::env::var("LOGICRS_DISABLE_RULES")
                .map(|v| {
                    v.split(',')
                        .filter(|s| !s.is_empty())
                        .map(str::to_string)
                        .collect()
                })
                .unwrap_or_default(),
            trace: std::env::var("LOGICRS_TRACE_RULES").is_ok(),
        })
    }

    /// Clear the per-thread fired-rule log.
    pub fn reset() {
        FIRED.with(|f| f.borrow_mut().clear());
    }

    /// Names of the rules that fired on this thread since the last `reset()`, in order.
    pub fn fired() -> Vec<&'static str> {
        FIRED.with(|f| f.borrow().clone())
    }

    /// Disable exactly these rules on the current thread (overrides `LOGICRS_DISABLE_RULES`).
    /// `None` restores the environment setting.
    pub fn set_disabled(rules: Option<&[&str]>) {
        DISABLED
            .with(|d| *d.borrow_mut() = rules.map(|r| r.iter().map(|s| s.to_string()).collect()));
    }

    pub(super) fn is_disabled(name: &str) -> bool {
        DISABLED.with(|d| match &*d.borrow() {
            Some(set) => set.contains(name),
            None => env().disabled.contains(name),
        })
    }

    pub(super) fn hit(name: &'static str, terms: &[super::Term], res: &super::Term) {
        FIRED.with(|f| f.borrow_mut().push(name));
        if env().trace {
            eprintln!("[logicrs rule] {name}: {terms:?} -> {res:?}");
        }
    }
}

struct RewritePipeline {
    level: OptLevel,
    rules: Vec<Box<dyn RewriteRule>>,
}

impl RewritePipeline {
    fn new(level: OptLevel) -> Self {
        Self {
            level,
            rules: Vec::new(),
        }
    }

    fn with_rule(mut self, rule: impl RewriteRule + 'static) -> Self {
        self.rules.push(Box::new(rule));
        self
    }
}

impl RewriteRule for RewritePipeline {
    fn opt_level(&self) -> OptLevel {
        self.level
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        for rule in self.rules.iter() {
            if !self.level.at_least(rule.opt_level()) {
                continue;
            }
            let name = rule.name();
            if audit::is_disabled(name) {
                continue;
            }
            if let Some(res) = rule.apply(terms) {
                audit::hit(name, terms, &res);
                return Some(res);
            }
        }
        None
    }
}

fn msb_bit_term(term: &Term) -> Option<Term> {
    if term.bv_len() == 1 {
        return Some(term.clone());
    }
    let op = term.try_op()?;
    if op.op == Concat || op.op == Sext {
        msb_bit_term(&op[0])
    } else {
        None
    }
}

fn collect_assoc_terms(op: FolOp, term: &Term, out: &mut Vec<Term>) {
    if let Some(top) = term.try_op()
        && top.op == op
    {
        collect_assoc_terms(op, &top[0], out);
        collect_assoc_terms(op, &top[1], out);
        return;
    }
    out.push(term.clone());
}

/// Fold `op` over constant operands through the simulator. Returns `None` when the simulated
/// value still contains X, so that the term stays unfolded instead of asserting.
fn eval_const_op(op: FolOp, terms: &[Term]) -> TermResult {
    let vals: Vec<Value> = terms
        .iter()
        .map(|t| Value::Bv(t.try_bv_const().unwrap().clone().into()))
        .collect();
    let lbv = op.simulate(&vals).into_bv().ok()?;
    if lbv.any_x() {
        return None;
    }
    Some(Term::bv_const(BitVec::from(lbv)))
}

fn fold_assoc_const_terms(op: FolOp, terms: &[Term]) -> TermResult {
    if !op.traits().contains(OpTrait::Associative) {
        return None;
    }

    let mut leaves = Vec::new();
    for term in terms {
        collect_assoc_terms(op, term, &mut leaves);
    }

    if leaves.len() <= 2 {
        return None;
    }

    let mut const_terms = Vec::new();
    let mut other_terms = Vec::new();
    for leaf in leaves {
        if leaf.is_const() {
            const_terms.push(leaf);
        } else {
            other_terms.push(leaf);
        }
    }

    if const_terms.len() <= 1 {
        return None;
    }

    let mut const_terms = const_terms.into_iter();
    let mut folded_const = const_terms.next().unwrap();
    for term in const_terms {
        folded_const = eval_const_op(op, &[folded_const, term])?;
    }
    other_terms.push(folded_const);
    other_terms.sort_by_key(|t| t.id());

    Some(Term::new_op_fold(op, other_terms))
}

fn slice_bit_literal(term: &Term) -> Option<(Term, usize, bool)> {
    let (inner, positive) = if let Some(top) = term.try_op()
        && top.op == Not
    {
        (&top[0], false)
    } else {
        (term, true)
    };

    let op = inner.try_op()?;
    if op.op != Slice {
        return None;
    }
    let base = op[0].clone();
    let h = op[1].bv_len();
    let l = op[2].bv_len();
    if h != l {
        return None;
    }
    Some((base, h, positive))
}

fn eq_slice_const(term: &Term) -> Option<(Term, usize, usize, Term)> {
    let op = term.try_op()?;
    if op.op != Eq {
        return None;
    }

    let (slice, cst) = if op[0].try_bv_const().is_some() {
        (&op[1], &op[0])
    } else if op[1].try_bv_const().is_some() {
        (&op[0], &op[1])
    } else {
        return None;
    };

    let sop = slice.try_op()?;
    if sop.op != Slice {
        return None;
    }
    let base = sop[0].clone();
    let h = sop[1].bv_len();
    let l = sop[2].bv_len();
    if h < l {
        return None;
    }
    Some((base, l, h, cst.clone()))
}

fn eq_term_const(term: &Term) -> Option<(Term, BitVec)> {
    let op = term.try_op()?;
    if op.op != Eq {
        return None;
    }

    if let Some(c) = op[0].try_bv_const() {
        return Some((op[1].clone(), c.clone()));
    }
    if let Some(c) = op[1].try_bv_const() {
        return Some((op[0].clone(), c.clone()));
    }
    None
}

fn bool_mask_ite(term: &Term) -> Option<(Term, bool)> {
    let op = term.try_op()?;

    if op.op != Ite {
        return None;
    }

    let tc = op[1].try_bv_const()?;
    let ec = op[2].try_bv_const()?;
    if tc.is_ones() && ec.is_zero() {
        Some((op[0].clone(), true))
    } else if tc.is_zero() && ec.is_ones() {
        Some((op[0].clone(), false))
    } else {
        None
    }
}

fn nonnegative_value_bits(term: &Term) -> Option<usize> {
    if let Some(c) = term.try_bv_const() {
        if c.sign_bit() {
            return None;
        }
        return Some(c.iter().rposition(|bit| bit).map_or(0, |idx| idx + 1));
    }

    let op = term.try_op()?;
    match op.op {
        Concat => {
            let prefix = op[0].try_bv_const()?;
            if prefix.is_zero() {
                Some(op[1].bv_len())
            } else {
                None
            }
        }
        Sext => nonnegative_value_bits(&op[0]),
        _ => None,
    }
}

fn ite_zero_branch(term: &Term) -> Option<(Term, Term, bool)> {
    let op = term.try_op()?;
    if op.op != Ite {
        return None;
    }
    if op[2].try_bv_const().is_some_and(|c| c.is_zero()) {
        return Some((op[0].clone(), op[1].clone(), true));
    }
    if op[1].try_bv_const().is_some_and(|c| c.is_zero()) {
        return Some((op[0].clone(), op[2].clone(), false));
    }
    None
}

fn is_same_read(term: &Term, array: &Term, index: &Term) -> bool {
    term.try_op()
        .is_some_and(|op| op.op == Read && op[0] == *array && op[1] == *index)
}

fn single_bit_diff_idx(a: &BitVec, b: &BitVec) -> Option<usize> {
    if a.len() != b.len() {
        return None;
    }
    let mut diff_idx: Option<usize> = None;
    for (idx, (b1, b2)) in a.iter().zip(b.iter()).enumerate() {
        if b1 != b2 {
            if diff_idx.is_some() {
                return None;
            }
            diff_idx = Some(idx);
        }
    }
    diff_idx
}

fn or_eq_term_consts_one_bit_diff(x: &Term, c1: &BitVec, c2: &BitVec) -> Option<Term> {
    let w = c1.len();
    if w == 0 || w != c2.len() || x.bv_len() != w {
        return None;
    }

    let diff_idx = single_bit_diff_idx(c1, c2)?;
    if w == 1 {
        // (x == 0) | (x == 1) is a tautology.
        return Some(Term::bool_const(true));
    }

    // If the differing bit is at an edge, prefer a slice-based rewrite (no mask const).
    if diff_idx == 0 {
        let slice = x.slice(1, w - 1);
        let mut c = BitVec::zero(w - 1);
        for (idx, bit) in c1.iter().enumerate().skip(1) {
            c.set(idx - 1, bit);
        }
        return Some(slice.op1(Eq, Term::bv_const(c)));
    }
    if diff_idx == w - 1 {
        let slice = x.slice(0, w - 2);
        let mut c = BitVec::zero(w - 1);
        for (idx, bit) in c1.iter().enumerate().take(w - 1) {
            c.set(idx, bit);
        }
        return Some(slice.op1(Eq, Term::bv_const(c)));
    }

    // General case: mask out the differing bit.
    let mut mask = BitVec::ones(w);
    mask.set(diff_idx, false);
    let mask = Term::bv_const(mask);
    let masked = x & &mask;

    let mut c = c1.clone();
    c.set(diff_idx, false);
    let c = Term::bv_const(c);
    Some(masked.op1(Eq, &c))
}

struct NotBoolXorEqSwap;
impl RewriteRule for NotBoolXorEqSwap {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        if !x.is_bool() {
            return None;
        }
        let xop = x.try_op()?;
        if xop.op == Xor {
            Some(xop[0].op1(Eq, &xop[1]))
        } else if xop.op == Eq && xop[0].is_bool() {
            Some(xop[0].op1(Xor, &xop[1]))
        } else {
            None
        }
    }
}

struct NotIteConst;

impl RewriteRule for NotIteConst {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let xop = x.try_op()?;
        if xop.op != Ite {
            return None;
        }
        if xop[1].is_const() && xop[2].is_const() {
            TermResult::Some(xop[0].ite(!&xop[1], !&xop[2]))
        } else {
            None
        }
    }
}

pub(crate) fn not_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(NotBoolXorEqSwap)
        .with_rule(NotIteConst);
    pipeline.apply(terms)
}

struct AndConstPropagation;
impl RewriteRule for AndConstPropagation {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if let Some(ac) = a.try_bv_const() {
            if ac.is_ones() {
                return Some(b.clone());
            }
            if ac.is_zero() {
                return Some(a.clone());
            }
        }
        None
    }
}

struct AndComplement;
impl RewriteRule for AndComplement {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if a == !b {
            return Some(a.mk_bv_const_zero());
        }
        None
    }
}

struct AndBoolMask;
impl RewriteRule for AndBoolMask {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let mask = &terms[1];
        let (cond, positive) = bool_mask_ite(mask)?;
        let zero = x.mk_bv_const_zero();
        if positive {
            Some(cond.ite(x, zero))
        } else {
            Some(cond.ite(zero, x))
        }
    }
}

struct AndMergeNestedAnds;
impl RewriteRule for AndMergeNestedAnds {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != And {
            return None;
        }
        if b == aop[0] {
            return Some(b & &aop[1]);
        }
        if b == aop[1] {
            return Some(b & &aop[0]);
        }
        let bop = b.try_op()?;
        if bop.op == And {
            if aop[0] == bop[0] {
                return Some(&aop[0] & &aop[1] & &bop[1]);
            }
            if aop[0] == bop[1] {
                return Some(&aop[0] & &aop[1] & &bop[0]);
            }
            if aop[1] == bop[0] {
                return Some(&aop[1] & &aop[0] & &bop[1]);
            }
            if aop[1] == bop[1] {
                return Some(&aop[1] & &aop[0] & &bop[0]);
            }
        }
        None
    }
}

struct AndDeMorganNotNot;
impl RewriteRule for AndDeMorganNotNot {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op == Not
            && let Some(bop) = b.try_op()
            && bop.op == Not
        {
            return Some(!(&aop[0] | &bop[0]));
        }
        None
    }
}

struct AndAbsorbComplementInOr;
impl RewriteRule for AndAbsorbComplementInOr {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let bop = b.try_op()?;
        if bop.op != Or {
            return None;
        }

        let not_a = !a.clone();
        if bop[0] == not_a {
            return Some(a & &bop[1]);
        }
        if bop[1] == not_a {
            return Some(a & &bop[0]);
        }

        if a == !&bop[0] {
            return Some(a & &bop[1]);
        }
        if a == !&bop[1] {
            return Some(a & &bop[0]);
        }
        None
    }
}

struct AndDistributeOverOr;
impl RewriteRule for AndDistributeOverOr {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != Or {
            return None;
        }

        if aop[0] == *b || aop[1] == *b {
            return Some(b.clone());
        }

        let bop = b.try_op()?;
        if bop.op == Or {
            if aop[0] == bop[0] {
                return Some(&aop[0] | (&aop[1] & &bop[1]));
            }
            if aop[0] == bop[1] {
                return Some(&aop[0] | (&aop[1] & &bop[0]));
            }
            if aop[1] == bop[0] {
                return Some(&aop[1] | (&aop[0] & &bop[1]));
            }
            if aop[1] == bop[1] {
                return Some(&aop[1] | (&aop[0] & &bop[0]));
            }
        }
        None
    }
}

struct AndMergeAdjacentEqSliceConsts;
impl RewriteRule for AndMergeAdjacentEqSliceConsts {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // eq(slice(x, l1..h1), c1) & eq(slice(x, l2..h2), c2)
        //  => eq(slice(x, min(l1,l2)..max(h1,h2)), concat(c_hi, c_lo))
        if a.is_bool()
            && let (Some((base1, l1, h1, c1)), Some((base2, l2, h2, c2))) =
                (eq_slice_const(a), eq_slice_const(b))
            && base1 == base2
        {
            if h1 + 1 == l2 {
                let rhs = Term::new_op(Concat, [c2.clone(), c1.clone()]);
                return Some(base1.slice(l1, h2).op1(Eq, &rhs));
            }
            if h2 + 1 == l1 {
                let rhs = Term::new_op(Concat, [c1.clone(), c2.clone()]);
                return Some(base1.slice(l2, h1).op1(Eq, &rhs));
            }
        }
        None
    }
}

struct AndBitLevelEqReconstruction;
impl RewriteRule for AndBitLevelEqReconstruction {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x[i] & ... & x[j]) == <const> (bit-level equality reconstruction)
        if !a.is_bool() {
            return None;
        }
        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::And, a, &mut leaves);
        collect_assoc_terms(FolOp::And, b, &mut leaves);

        let mut base: Option<Term> = None;
        let mut bits_by_idx = std::collections::BTreeMap::<usize, bool>::new();
        for leaf in leaves.iter() {
            let (b, idx, bit_is_one) = slice_bit_literal(leaf)?;
            if let Some(ref bb) = base {
                if *bb != b {
                    return None;
                }
            } else {
                base = Some(b);
            }
            if let Some(prev) = bits_by_idx.insert(idx, bit_is_one)
                && prev != bit_is_one
            {
                return Some(a.mk_bv_const_zero());
            }
        }
        let base = base?;
        let (lo, _) = bits_by_idx.first_key_value()?;
        let (hi, _) = bits_by_idx.last_key_value()?;
        let (lo, hi) = (*lo, *hi);
        if bits_by_idx.len() == hi - lo + 1 {
            let slice = base.slice(lo, hi);
            let mut rhs = BitVec::zero(hi - lo + 1);
            for (idx, bit_is_one) in bits_by_idx.iter() {
                rhs.set(idx - lo, *bit_is_one);
            }
            let rhs = Term::bv_const(rhs);
            return Some(slice.op1(Eq, &rhs));
        }
        None
    }
}

struct AndBitLevelMaskedEqReconstruction;
impl RewriteRule for AndBitLevelMaskedEqReconstruction {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x[i]=c1) & (x[j]=c2) & ...  =>  ((slice(x, lo..hi) & mask) == rhs)
        // Works even when indices are not contiguous (mask has zeros for gaps).
        if !a.is_bool() {
            return None;
        }

        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::And, a, &mut leaves);
        collect_assoc_terms(FolOp::And, b, &mut leaves);

        let mut base: Option<Term> = None;
        let mut bits_by_idx = std::collections::BTreeMap::<usize, bool>::new();
        for leaf in leaves.iter() {
            let (b, idx, bit_is_one) = slice_bit_literal(leaf)?;
            if let Some(ref bb) = base {
                if *bb != b {
                    return None;
                }
            } else {
                base = Some(b);
            }
            if let Some(prev) = bits_by_idx.insert(idx, bit_is_one)
                && prev != bit_is_one
            {
                return Some(a.mk_bv_const_zero());
            }
        }

        // Heuristic: only rewrite when there are enough constrained bits to offset
        // the extra mask/eq/slice nodes this introduces.
        if bits_by_idx.len() < 8 {
            return None;
        }

        let base = base?;
        let (lo, _) = bits_by_idx.first_key_value()?;
        let (hi, _) = bits_by_idx.last_key_value()?;
        let (lo, hi) = (*lo, *hi);
        let w = hi - lo + 1;

        let slice = base.slice(lo, hi);
        let mut mask = BitVec::zero(w);
        let mut rhs = BitVec::zero(w);
        for (idx, bit_is_one) in bits_by_idx.iter() {
            let pos = idx - lo;
            mask.set(pos, true);
            rhs.set(pos, *bit_is_one);
        }
        let rhs = Term::bv_const(rhs);

        if mask.is_ones() {
            return Some(slice.op1(Eq, &rhs));
        }

        let mask = Term::bv_const(mask);
        let masked = &slice & &mask;
        Some(masked.op1(Eq, &rhs))
    }
}

pub(crate) fn and_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(AndConstPropagation)
        .with_rule(AndComplement)
        .with_rule(AndBoolMask)
        .with_rule(AndMergeNestedAnds)
        .with_rule(AndDeMorganNotNot)
        .with_rule(AndAbsorbComplementInOr)
        .with_rule(AndDistributeOverOr)
        .with_rule(AndMergeAdjacentEqSliceConsts)
        .with_rule(AndBitLevelEqReconstruction)
        .with_rule(AndBitLevelMaskedEqReconstruction);
    pipeline.apply(terms)
}

struct OrConstPropagation;
impl RewriteRule for OrConstPropagation {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if let Some(ac) = a.try_bv_const() {
            if ac.is_ones() {
                return Some(a.clone());
            }
            if ac.is_zero() {
                return Some(b.clone());
            }
        }
        None
    }
}

struct OrComplement;
impl RewriteRule for OrComplement {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if a == !b {
            return Some(a.mk_bv_const_ones());
        }
        None
    }
}

struct OrMergeNestedOrs;
impl RewriteRule for OrMergeNestedOrs {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != Or {
            return None;
        }
        if b == aop[0] {
            return Some(b | &aop[1]);
        }
        if b == aop[1] {
            return Some(b | &aop[0]);
        }
        let bop = b.try_op()?;
        if bop.op == Or {
            if aop[0] == bop[0] {
                return Some(&aop[0] | &aop[1] | &bop[1]);
            }
            if aop[0] == bop[1] {
                return Some(&aop[0] | &aop[1] | &bop[0]);
            }
            if aop[1] == bop[0] {
                return Some(&aop[1] | &aop[0] | &bop[1]);
            }
            if aop[1] == bop[1] {
                return Some(&aop[1] | &aop[0] | &bop[0]);
            }
        }
        None
    }
}

struct OrDeMorganNotNot;
impl RewriteRule for OrDeMorganNotNot {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op == Not
            && let Some(bop) = b.try_op()
            && bop.op == Not
        {
            return Some(!(&aop[0] & &bop[0]));
        }
        None
    }
}

struct OrAbsorbComplementInAnd;
impl RewriteRule for OrAbsorbComplementInAnd {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let bop = b.try_op()?;
        if bop.op != And {
            return None;
        }

        let not_a = !a.clone();
        if bop[0] == not_a {
            return Some(a | &bop[1]);
        }
        if bop[1] == not_a {
            return Some(a | &bop[0]);
        }

        if a == !&bop[0] {
            return Some(a | &bop[1]);
        }
        if a == !&bop[1] {
            return Some(a | &bop[0]);
        }
        None
    }
}

struct OrAbsorbIteCond;
impl RewriteRule for OrAbsorbIteCond {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != Ite {
            return None;
        }
        if b == aop[0] {
            return Some(b | &aop[2]);
        }
        if b == !&aop[0] {
            return Some(b | &aop[1]);
        }
        None
    }
}

struct OrMergeIteZeroBranches;
impl RewriteRule for OrMergeIteZeroBranches {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let (ac, av, a_when_true) = ite_zero_branch(a)?;
        let (bc, bv, b_when_true) = ite_zero_branch(b)?;
        if ac != bc {
            return None;
        }

        match (a_when_true, b_when_true) {
            (true, false) => Some(ac.ite(av, bv)),
            (false, true) => Some(ac.ite(bv, av)),
            (true, true) => {
                let zero = a.mk_bv_const_zero();
                Some(ac.ite(av | bv, zero))
            }
            (false, false) => {
                let zero = a.mk_bv_const_zero();
                Some(ac.ite(zero, av | bv))
            }
        }
    }
}

struct OrDistributeOverAnd;
impl RewriteRule for OrDistributeOverAnd {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != And {
            return None;
        }

        if aop[0] == *b || aop[1] == *b {
            return Some(b.clone());
        }

        let bop = b.try_op()?;
        if bop.op == And {
            if aop[0] == bop[0] {
                return Some(&aop[0] & (&aop[1] | &bop[1]));
            }
            if aop[0] == bop[1] {
                return Some(&aop[0] & (&aop[1] | &bop[0]));
            }
            if aop[1] == bop[0] {
                return Some(&aop[1] & (&aop[0] | &bop[1]));
            }
            if aop[1] == bop[1] {
                return Some(&aop[1] & (&aop[0] | &bop[0]));
            }
        }
        None
    }
}

struct OrMergeEqConstOneBitDiff;
impl RewriteRule for OrMergeEqConstOneBitDiff {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x == c1) | (x == c2) where c1,c2 differ by exactly one bit.
        let (x, c1) = eq_term_const(a)?;
        let (y, c2) = eq_term_const(b)?;
        if x != y {
            return None;
        }
        or_eq_term_consts_one_bit_diff(&x, &c1, &c2)
    }
}

struct OrMergeEqConstOneBitDiffAssoc;
impl RewriteRule for OrMergeEqConstOneBitDiffAssoc {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if !a.is_bool() {
            return None;
        }

        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::Or, a, &mut leaves);
        collect_assoc_terms(FolOp::Or, b, &mut leaves);
        if leaves.len() <= 2 {
            return None;
        }

        let mut seen = GHashMap::<Term, Vec<(usize, BitVec)>>::new();
        for (idx, leaf) in leaves.iter().enumerate() {
            let Some((t, c)) = eq_term_const(leaf) else {
                continue;
            };

            if let Some(prevs) = seen.get(&t) {
                for (prev_idx, prev_c) in prevs.iter() {
                    if let Some(merged) = or_eq_term_consts_one_bit_diff(&t, prev_c, &c) {
                        let (i, j) = if *prev_idx < idx {
                            (*prev_idx, idx)
                        } else {
                            (idx, *prev_idx)
                        };
                        let mut new_leaves = Vec::with_capacity(leaves.len() - 1);
                        for (k, leaf) in leaves.iter().enumerate() {
                            if k == i {
                                new_leaves.push(merged.clone());
                            } else if k == j {
                                continue;
                            } else {
                                new_leaves.push(leaf.clone());
                            }
                        }

                        let mut acc = new_leaves[0].clone();
                        for leaf in new_leaves.iter().skip(1) {
                            acc = &acc | leaf;
                        }
                        return Some(acc);
                    }
                }
            }

            seen.entry(t).or_default().push((idx, c));
        }

        None
    }
}

struct OrBitLevelClauseReconstruction;
impl RewriteRule for OrBitLevelClauseReconstruction {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x[i] | ... | x[j]) != <const> (bit-level clause reconstruction)
        if !a.is_bool() {
            return None;
        }
        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::Or, a, &mut leaves);
        collect_assoc_terms(FolOp::Or, b, &mut leaves);

        let mut base: Option<Term> = None;
        let mut pol_by_idx = std::collections::BTreeMap::<usize, bool>::new();
        for leaf in leaves.iter() {
            let (b, idx, positive) = slice_bit_literal(leaf)?;
            if let Some(ref bb) = base {
                if *bb != b {
                    return None;
                }
            } else {
                base = Some(b);
            }
            if let Some(prev) = pol_by_idx.insert(idx, positive)
                && prev != positive
            {
                return Some(a.mk_bv_const_ones());
            }
        }
        let base = base?;
        let (lo, _) = pol_by_idx.first_key_value()?;
        let (hi, _) = pol_by_idx.last_key_value()?;
        let (lo, hi) = (*lo, *hi);
        if pol_by_idx.len() == hi - lo + 1 {
            let slice = base.slice(lo, hi);
            // a clause is false only if every literal is false
            let mut rhs = BitVec::zero(hi - lo + 1);
            for (idx, positive) in pol_by_idx.iter() {
                rhs.set(idx - lo, !positive);
            }
            let rhs = Term::bv_const(rhs);
            return Some(!slice.op1(Eq, &rhs));
        }
        None
    }
}

struct OrBitLevelMaskedClauseReconstruction;
impl RewriteRule for OrBitLevelMaskedClauseReconstruction {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x[i] | ... | x[j]) != <const> (bit-level clause reconstruction with gaps)
        // (x[i]=p1) | (x[j]=p2) | ...  =>  !((slice(x, lo..hi) & mask) == rhs)
        // where rhs encodes the unique assignment that falsifies every literal.
        if !a.is_bool() {
            return None;
        }

        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::Or, a, &mut leaves);
        collect_assoc_terms(FolOp::Or, b, &mut leaves);

        let mut base: Option<Term> = None;
        let mut pol_by_idx = std::collections::BTreeMap::<usize, bool>::new();
        for leaf in leaves.iter() {
            let (b, idx, positive) = slice_bit_literal(leaf)?;
            if let Some(ref bb) = base {
                if *bb != b {
                    return None;
                }
            } else {
                base = Some(b);
            }
            if let Some(prev) = pol_by_idx.insert(idx, positive)
                && prev != positive
            {
                return Some(a.mk_bv_const_ones());
            }
        }

        // Heuristic: only rewrite when there are enough constrained bits to offset
        // the extra mask/eq/slice nodes this introduces.
        if pol_by_idx.len() < 8 {
            return None;
        }

        let base = base?;
        let (lo, _) = pol_by_idx.first_key_value()?;
        let (hi, _) = pol_by_idx.last_key_value()?;
        let (lo, hi) = (*lo, *hi);
        let w = hi - lo + 1;

        let slice = base.slice(lo, hi);
        let mut mask = BitVec::zero(w);
        let mut rhs = BitVec::zero(w);
        for (idx, positive) in pol_by_idx.iter() {
            let pos = idx - lo;
            mask.set(pos, true);
            rhs.set(pos, !positive);
        }
        let rhs = Term::bv_const(rhs);

        if mask.is_ones() {
            return Some(!slice.op1(Eq, &rhs));
        }

        let mask = Term::bv_const(mask);
        let masked = &slice & &mask;
        Some(!masked.op1(Eq, &rhs))
    }
}

pub(crate) fn or_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(OrConstPropagation)
        .with_rule(OrComplement)
        .with_rule(OrMergeNestedOrs)
        .with_rule(OrDeMorganNotNot)
        .with_rule(OrAbsorbComplementInAnd)
        .with_rule(OrDistributeOverAnd)
        .with_rule(OrAbsorbIteCond)
        .with_rule(OrMergeIteZeroBranches)
        .with_rule(OrMergeEqConstOneBitDiff)
        .with_rule(OrMergeEqConstOneBitDiffAssoc)
        .with_rule(OrBitLevelClauseReconstruction)
        .with_rule(OrBitLevelMaskedClauseReconstruction);
    pipeline.apply(terms)
}

struct XorConstPropagation;
impl RewriteRule for XorConstPropagation {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if let Some(ac) = a.try_bv_const() {
            if ac.is_ones() {
                return Some(!b.clone());
            }
            if ac.is_zero() {
                return Some(b.clone());
            }
        }
        None
    }
}

struct XorSelf;
impl RewriteRule for XorSelf {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if a == b {
            return Some(a.mk_bv_const_zero());
        }
        None
    }
}

struct XorComplement;
impl RewriteRule for XorComplement {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if a == !b {
            return Some(a.mk_bv_const_ones());
        }
        None
    }
}

pub(crate) fn xor_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(XorConstPropagation)
        .with_rule(XorSelf)
        .with_rule(XorComplement);
    pipeline.apply(terms)
}

struct EqBoolViaXor;
impl RewriteRule for EqBoolViaXor {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if !x.is_bool() {
            return None;
        }

        // eq(x,y) = !xor(x,y), reusing (a subset of) xor simplifications without needing ctx.
        let xor_simplified = if let Some(xc) = x.try_bv_const() {
            if xc.is_ones() {
                Some(!y.clone())
            } else if xc.is_zero() {
                Some(y.clone())
            } else {
                None
            }
        } else if x == y {
            Some(x.mk_bv_const_zero())
        } else if x == !y {
            Some(x.mk_bv_const_ones())
        } else {
            None
        }?;
        Some(!xor_simplified)
    }
}

struct EqRefl;
impl RewriteRule for EqRefl {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if x == y {
            return Some(Term::bool_const(true));
        }
        None
    }
}

struct EqComplement;
impl RewriteRule for EqComplement {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if x == !y {
            return Some(Term::bool_const(false));
        }
        None
    }
}

struct EqBoolMaskConst;
impl RewriteRule for EqBoolMaskConst {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        let (cond, positive) = bool_mask_ite(x)?;
        let yc = y.try_bv_const()?;
        if yc.is_zero() {
            return Some(cond.not_if(positive));
        }
        if yc.is_ones() {
            return Some(cond.not_if(!positive));
        }
        None
    }
}

struct EqNotConst;
impl RewriteRule for EqNotConst {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];

        // eq(!x, !y) => eq(x, y)
        if let Some(xop) = x.try_op()
            && xop.op == Not
            && let Some(yop) = y.try_op()
            && yop.op == Not
        {
            return Some(xop[0].op1(Eq, &yop[0]));
        }

        // eq(!x, c) => eq(x, !c) (push Not into constant)
        if let Some(yc) = y.try_bv_const()
            && let Some(xop) = x.try_op()
            && xop.op == Not
        {
            let mut nc = BitVec::zero(yc.len());
            for (idx, bit) in yc.iter().enumerate() {
                nc.set(idx, !bit);
            }
            return Some(xop[0].op1(Eq, Term::bv_const(nc)));
        }

        // eq(c, !x) => eq(x, !c) (symmetry)
        if let Some(xc) = x.try_bv_const()
            && let Some(yop) = y.try_op()
            && yop.op == Not
        {
            let mut nc = BitVec::zero(xc.len());
            for (idx, bit) in xc.iter().enumerate() {
                nc.set(idx, !bit);
            }
            return Some(yop[0].op1(Eq, Term::bv_const(nc)));
        }

        None
    }
}

struct EqXorZero;
impl RewriteRule for EqXorZero {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];

        // eq(xor(a,b), 0) => eq(a,b)
        let (xor_term, cst) = if let Some(xc) = x.try_bv_const() {
            (y, xc)
        } else {
            let yc = y.try_bv_const()?;
            (x, yc)
        };
        if !cst.is_zero() {
            return None;
        }
        let xop = xor_term.try_op()?;
        if xop.op != Xor {
            return None;
        }
        Some(xop[0].op1(Eq, &xop[1]))
    }
}

struct EqAndConst;
impl RewriteRule for EqAndConst {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];

        let xop = x.try_op()?;
        if xop.op != And {
            return None;
        }
        let yc = y.try_bv_const()?;

        let mask = if let Some(mc) = xop[0].try_bv_const() {
            mc
        } else {
            xop[1].try_bv_const()?
        };

        for (idx, bit) in yc.iter().enumerate() {
            if bit && !mask.get(idx) {
                return Some(Term::bool_const(false));
            }
        }

        None
    }
}

pub(crate) fn eq_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(EqBoolViaXor)
        .with_rule(EqRefl)
        .with_rule(EqComplement)
        .with_rule(EqBoolMaskConst)
        .with_rule(EqNotConst)
        .with_rule(EqXorZero)
        .with_rule(EqAndConst);
    pipeline.apply(terms)
}

struct UltConstX;
impl RewriteRule for UltConstX {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if let Some(xc) = x.try_bv_const() {
            if xc.is_zero() {
                return Some(!x.op1(Eq, y));
            }
            if xc.is_ones() {
                return Some(Term::bool_const(false));
            }
        }
        None
    }
}

struct UltConstY;
impl RewriteRule for UltConstY {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if let Some(yc) = y.try_bv_const() {
            if yc.is_zero() {
                return Some(Term::bool_const(false));
            }
            if yc.is_ones() {
                return Some(!x.op1(Eq, y));
            }
        }
        None
    }
}

struct UltConcatConst;
impl RewriteRule for UltConcatConst {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];

        // Case 1: ult(concat(zeros, x_sub), cst)
        if let Some(xop) = x.try_op()
            && xop.op == Concat
            && let Some(xc_hi) = xop[0].try_bv_const()
            && xc_hi.is_zero()
            && let Some(yc) = y.try_bv_const()
        {
            let lo_len = xop[1].bv_len();
            let hi_len = xop[0].bv_len();

            let y_l = yc.slice(0..lo_len);
            let y_h = yc.slice(lo_len..lo_len + hi_len);

            if !y_h.is_zero() {
                return Some(Term::bool_const(true));
            } else {
                return Some(xop[1].op1(Ult, Term::bv_const(y_l)));
            }
        }

        // Case 2: ult(cst, concat(zeros, y_sub))
        if let Some(yop) = y.try_op()
            && yop.op == Concat
            && let Some(yc_hi) = yop[0].try_bv_const()
            && yc_hi.is_zero()
            && let Some(xc) = x.try_bv_const()
        {
            let lo_len = yop[1].bv_len();
            let hi_len = yop[0].bv_len();

            let cst_lo = xc.slice(0..lo_len);

            let cst_hi = xc.slice(lo_len..lo_len + hi_len);

            if !cst_hi.is_zero() {
                return Some(Term::bool_const(false));
            } else {
                return Some(Term::bv_const(cst_lo).op1(Ult, &yop[1]));
            }
        }

        None
    }
}

pub(crate) fn ult_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(UltConstX)
        .with_rule(UltConstY)
        .with_rule(UltConcatConst);
    pipeline.apply(terms)
}

fn is_signed_min(c: &BitVec) -> bool {
    if !c.sign_bit() {
        return false;
    }
    c.iter().take(c.len() - 1).all(|bit| !bit)
}

fn is_signed_max(c: &BitVec) -> bool {
    if c.sign_bit() {
        return false;
    }
    c.iter().take(c.len() - 1).all(|bit| bit)
}

struct SltRefl;
impl RewriteRule for SltRefl {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if x == y {
            return Some(Term::bool_const(false));
        }
        None
    }
}

struct SltConstX;
impl RewriteRule for SltConstX {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        let xc = x.try_bv_const()?;
        if is_signed_min(xc) {
            return Some(!x.op1(Eq, y));
        }
        if is_signed_max(xc) {
            return Some(Term::bool_const(false));
        }
        None
    }
}

struct SltConstY;
impl RewriteRule for SltConstY {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        let yc = y.try_bv_const()?;
        if is_signed_min(yc) {
            return Some(Term::bool_const(false));
        }
        if is_signed_max(yc) {
            return Some(!x.op1(Eq, y));
        }
        None
    }
}

struct SltNonnegativeBound;
impl RewriteRule for SltNonnegativeBound {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        let yc = y.try_bv_const()?;
        let x_bits = nonnegative_value_bits(x)?;

        if yc.is_zero() || yc.sign_bit() {
            return Some(Term::bool_const(false));
        }
        if yc.iter().enumerate().any(|(idx, bit)| bit && idx >= x_bits) {
            return Some(Term::bool_const(true));
        }
        None
    }
}

pub(crate) fn slt_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(SltRefl)
        .with_rule(SltConstX)
        .with_rule(SltConstY)
        .with_rule(SltNonnegativeBound);
    pipeline.apply(terms)
}

struct IteConstCond;
impl RewriteRule for IteConstCond {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
        let cc = c.try_bv_const()?;
        if cc.is_ones() {
            return Some(t.clone());
        }
        Some(e.clone())
    }
}

struct IteSameBranches;
impl RewriteRule for IteSameBranches {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let t = &terms[1];
        let e = &terms[2];
        if t == e {
            return Some(t.clone());
        }
        None
    }
}

struct IteNotCondSwap;
impl RewriteRule for IteNotCondSwap {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
        let cop = c.try_op()?;
        if cop.op == Not {
            return Some(cop[0].ite(e, t));
        }
        None
    }
}

struct IteNotBranches;
impl RewriteRule for IteNotBranches {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
        let top = t.try_op()?;
        let eop = e.try_op()?;
        if top.op == eop.op && (top.op == Not || top.op == Neg) {
            return Some(c.ite(&top[0], &eop[0]).op0(top.op));
        }
        None
    }
}

struct IteBoolComplementBranches;
impl RewriteRule for IteBoolComplementBranches {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
        if !t.is_bool() {
            return None;
        }

        // ite(c, x, !x) => eq(c, x)
        if e == !t {
            return Some(c.op1(Eq, t));
        }
        // ite(c, !x, x) => xor(c, x)
        if t == !e {
            return Some(c ^ e);
        }
        None
    }
}

struct IteBoolBranchConst;
impl RewriteRule for IteBoolBranchConst {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
        if !t.is_bool() {
            return None;
        }

        if let Some(ec) = e.try_bv_const() {
            if ec.is_zero() {
                return Some(c & t);
            }
            if ec.is_ones() {
                return Some(!c | t);
            }
        }
        if let Some(tc) = t.try_bv_const() {
            if tc.is_zero() {
                return Some(!c & e);
            }
            if tc.is_ones() {
                return Some(c | e);
            }
        }
        None
    }
}

struct IteSameCondNested;
impl RewriteRule for IteSameCondNested {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);

        if let Some(top) = t.try_op()
            && top.op == Ite
            && top[0] == *c
        {
            return Some(c.ite(&top[1], e));
        }

        if let Some(eop) = e.try_op()
            && eop.op == Ite
            && eop[0] == *c
        {
            return Some(c.ite(t, &eop[2]));
        }

        None
    }
}

struct IteNestedSharedBranch;
impl RewriteRule for IteNestedSharedBranch {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);

        if let Some(top) = t.try_op()
            && top.op == Ite
        {
            if top[2] == *e {
                return Some((c & &top[0]).ite(&top[1], e));
            }
            if top[1] == *e {
                return Some((c & !&top[0]).ite(&top[2], e));
            }
        }

        if let Some(eop) = e.try_op()
            && eop.op == Ite
        {
            if eop[1] == *t {
                return Some((c | &eop[0]).ite(t, &eop[2]));
            }
            if eop[2] == *t {
                return Some((c | !&eop[0]).ite(t, &eop[1]));
            }
        }

        None
    }
}

struct IteWriteBranches;
impl RewriteRule for IteWriteBranches {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);

        if let (Some(top), Some(eop)) = (t.try_op(), e.try_op())
            && top.op == Write
            && eop.op == Write
            && top[0] == eop[0]
            && top[1] == eop[1]
        {
            let value = c.ite(&top[2], &eop[2]);
            return Some(Term::new_op(Write, [top[0].clone(), top[1].clone(), value]));
        }

        if let Some(top) = t.try_op()
            && top.op == Write
            && top[0] == *e
            && let Some(vop) = top[2].try_op()
            && vop.op == Ite
            && vop[0] == *c
        {
            if is_same_read(&vop[2], &top[0], &top[1]) {
                return Some(t.clone());
            }
            if is_same_read(&vop[1], &top[0], &top[1]) {
                return Some(e.clone());
            }
        }

        if let Some(eop) = e.try_op()
            && eop.op == Write
            && eop[0] == *t
            && let Some(vop) = eop[2].try_op()
            && vop.op == Ite
            && vop[0] == *c
        {
            if is_same_read(&vop[1], &eop[0], &eop[1]) {
                return Some(e.clone());
            }
            if is_same_read(&vop[2], &eop[0], &eop[1]) {
                return Some(t.clone());
            }
        }

        None
    }
}

pub(crate) fn ite_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(IteConstCond)
        .with_rule(IteSameBranches)
        .with_rule(IteNotCondSwap)
        .with_rule(IteNotBranches)
        .with_rule(IteBoolComplementBranches)
        .with_rule(IteBoolBranchConst)
        .with_rule(IteSameCondNested)
        .with_rule(IteNestedSharedBranch)
        .with_rule(IteWriteBranches);
    pipeline.apply(terms)
}

struct ConcatConst;
impl RewriteRule for ConcatConst {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        let (xc, yc) = (x.try_bv_const()?, y.try_bv_const()?);
        let mut c = yc.clone();
        c.extend(xc.iter());
        Some(Term::bv_const(c))
    }
}

struct ConcatAssocConstPrefix;
impl RewriteRule for ConcatAssocConstPrefix {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];

        // concat(c1, concat(c2, t)) => concat(concat(c1,c2), t)
        // (exposes constant folding on concat(c1,c2))
        x.try_bv_const()?;
        let yop = y.try_op()?;
        if yop.op != Concat {
            return None;
        }
        yop[0].try_bv_const()?;

        let hi = Term::new_op(Concat, [x.clone(), yop[0].clone()]);
        Some(hi.op1(Concat, &yop[1]))
    }
}

struct ConcatSignExtBySlice;
impl RewriteRule for ConcatSignExtBySlice {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if y.bv_len() == 0 || x.bv_len() != 1 {
            return None;
        }
        let xop = x.try_op()?;
        if xop.op != Slice || xop[0] != *y {
            return None;
        }
        let idx = y.bv_len() - 1;
        if xop[1].bv_len() == idx && xop[2].bv_len() == idx {
            return Some(Term::new_op(Sext, [y.clone(), Term::bool_const(false)]));
        }
        None
    }
}

struct ConcatSignExtBySextSlice;
impl RewriteRule for ConcatSignExtBySextSlice {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if y.bv_len() == 0 || x.bv_len() != 1 {
            return None;
        }

        let yop = y.try_op()?;
        if yop.op != Sext {
            return None;
        }
        let xop = x.try_op()?;
        if xop.op != Slice || xop[0] != yop[0] {
            return None;
        }
        let inner = &yop[0];
        if inner.bv_len() == 0 {
            return None;
        }
        let idx = inner.bv_len() - 1;
        if xop[1].bv_len() == idx && xop[2].bv_len() == idx {
            return Some(Term::new_op(
                Sext,
                [
                    inner.clone(),
                    Term::bv_const(BitVec::zero(yop[1].bv_len() + 1)),
                ],
            ));
        }
        None
    }
}

struct ConcatSignExtByMsbTerm;
impl RewriteRule for ConcatSignExtByMsbTerm {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if y.bv_len() == 0 || x.bv_len() != 1 {
            return None;
        }
        if let Some(msb) = msb_bit_term(y)
            && msb == *x
        {
            return Some(Term::new_op(Sext, [y.clone(), Term::bool_const(false)]));
        }
        None
    }
}

pub(crate) fn concat_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(ConcatConst)
        .with_rule(ConcatAssocConstPrefix)
        .with_rule(ConcatSignExtBySlice)
        .with_rule(ConcatSignExtBySextSlice)
        .with_rule(ConcatSignExtByMsbTerm);
    pipeline.apply(terms)
}

struct SextZeroExt;
impl RewriteRule for SextZeroExt {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let ext = terms[1].bv_len();
        if ext == 0 {
            return Some(x.clone());
        }
        None
    }
}

struct SextBoolToIte;

impl RewriteRule for SextBoolToIte {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let ext = terms[1].bv_len();
        if !x.is_bool() {
            return None;
        }
        TermResult::Some(x.ite(
            Term::bv_const(BitVec::ones(ext + 1)),
            Term::bv_const(BitVec::zero(ext + 1)),
        ))
    }
}

struct SextMergeNested;
impl RewriteRule for SextMergeNested {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let ext = terms[1].bv_len();
        let xop = x.try_op()?;
        if xop.op != Sext {
            return None;
        }
        let inner = &xop[0];
        let inner_ext = xop[1].bv_len();
        Some(Term::new_op(
            Sext,
            [inner.clone(), Term::bv_const(BitVec::zero(inner_ext + ext))],
        ))
    }
}

pub(crate) fn sext_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(SextZeroExt)
        .with_rule(SextBoolToIte)
        .with_rule(SextMergeNested);
    pipeline.apply(terms)
}

struct SliceWholeRange;
impl RewriteRule for SliceWholeRange {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        if l == 0 && h == s.bv_len() - 1 {
            return Some(s.clone());
        }
        None
    }
}

struct SliceOfSlice;
impl RewriteRule for SliceOfSlice {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        let sop = s.try_op()?;
        if sop.op != Slice {
            return None;
        }
        let base = &sop[0];
        let inner_l = sop[2].bv_len();
        let new_l = inner_l + l;
        let new_h = inner_l + h;
        Some(base.slice(new_l, new_h))
    }
}

struct SliceOfConcat;
impl RewriteRule for SliceOfConcat {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        let sop = s.try_op()?;
        if sop.op != Concat {
            return None;
        }

        let hi = &sop[0];
        let lo = &sop[1];
        let lo_len = lo.bv_len();
        if h < lo_len {
            return Some(lo.slice(l, h));
        }
        if l >= lo_len {
            return Some(hi.slice(l - lo_len, h - lo_len));
        }

        let hi_part = hi.slice(0, h - lo_len);
        let lo_part = lo.slice(l, lo_len - 1);
        Some(Term::new_op(Concat, [hi_part, lo_part]))
    }
}

struct SliceOfSext;
impl RewriteRule for SliceOfSext {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O0
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        let sop = s.try_op()?;
        if sop.op != Sext {
            return None;
        }

        let base = &sop[0];
        if h < base.bv_len() {
            return Some(base.slice(l, h));
        }
        if l >= base.bv_len() {
            let sign = base.sign_bit();
            return Some(Term::new_op(
                Sext,
                [sign, Term::bv_const(BitVec::zero(h - l))],
            ));
        }

        let ext_len = h - base.bv_len() + 1;
        Some(Term::new_op(
            Sext,
            [
                base.slice(l, base.bv_len() - 1),
                Term::bv_const(BitVec::zero(ext_len)),
            ],
        ))
    }
}

struct SliceOfIte;
impl RewriteRule for SliceOfIte {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        let sop = s.try_op()?;
        if sop.op != Ite {
            return None;
        }
        Some(sop[0].ite(sop[1].slice(l, h), sop[2].slice(l, h)))
    }
}

struct SliceOfBitwiseOp;
impl RewriteRule for SliceOfBitwiseOp {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        let sop = s.try_op()?;
        match sop.op {
            Not => Some(!sop[0].slice(l, h)),
            And | Or | Xor => Some(Term::new_op(
                sop.op,
                [sop[0].slice(l, h), sop[1].slice(l, h)],
            )),
            _ => None,
        }
    }
}

/// `slice(neg(x), 0, h) -> neg(slice(x, 0, h))`.
///
/// Only sound for `l == 0`: `neg(x) = not(x) + 1`, so bit `i` of `neg(x)` depends on
/// `x[0..i)` through the carry chain, and `slice(neg(x), l, h)` for `l > 0` cannot be
/// expressed as `neg(slice(x, l, h))` (e.g. `x = 0b11`: `neg(x)[1] = 0` but
/// `neg(x[1]) = 1`).
struct SliceOfNeg;
impl RewriteRule for SliceOfNeg {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        if l != 0 {
            return None;
        }
        let sop = s.try_op()?;
        match sop.op {
            Neg => Some(sop[0].slice(l, h).op0(Neg)),
            _ => None,
        }
    }
}

struct SliceLsbOfAdd;
impl RewriteRule for SliceLsbOfAdd {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        if l != 0 || h != 0 {
            return None;
        }
        let sop = s.try_op()?;
        if sop.op != Add {
            return None;
        }
        Some(sop[0].slice(0, 0) ^ sop[1].slice(0, 0))
    }
}

struct SliceLsbOfSll;
impl RewriteRule for SliceLsbOfSll {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        if l != 0 || h != 0 {
            return None;
        }
        let sop = s.try_op()?;
        if sop.op != Sll {
            return None;
        }
        let shift_is_zero = sop[1].op1(Eq, sop[1].mk_bv_const_zero());
        Some(shift_is_zero & sop[0].slice(0, 0))
    }
}

pub(crate) fn slice_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(SliceWholeRange)
        .with_rule(SliceOfSlice)
        .with_rule(SliceOfConcat)
        .with_rule(SliceOfSext)
        .with_rule(SliceOfIte)
        .with_rule(SliceOfBitwiseOp)
        .with_rule(SliceOfNeg)
        .with_rule(SliceLsbOfAdd)
        .with_rule(SliceLsbOfSll);
    pipeline.apply(terms)
}

struct AddByZero;
impl RewriteRule for AddByZero {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        let xc = x.try_bv_const()?;
        if xc.is_zero() {
            return Some(y.clone());
        }
        None
    }
}

pub(crate) fn add_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    RewritePipeline::new(ctx.level)
        .with_rule(AddByZero)
        .apply(terms)
}

struct NegBool;
impl RewriteRule for NegBool {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        if x.is_bool() {
            return TermResult::Some(x.clone());
        }
        None
    }
}

pub(crate) fn neg_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    RewritePipeline::new(ctx.level)
        .with_rule(NegBool)
        .apply(terms)
}

struct MulByZero;
impl RewriteRule for MulByZero {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let xc = x.try_bv_const()?;
        if xc.is_zero() {
            return Some(x.clone());
        }
        None
    }
}

struct MulByOne;
impl RewriteRule for MulByOne {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        let xc = x.try_bv_const()?;
        if xc.is_one() {
            return Some(y.clone());
        }
        None
    }
}

pub(crate) fn mul_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(MulByZero)
        .with_rule(MulByOne);
    pipeline.apply(terms)
}

pub(crate) fn udiv_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    // Placeholder: no rewrite rules yet.
    RewritePipeline::new(ctx.level).apply(terms)
}

struct ReadOverWriteSameIndex;
impl RewriteRule for ReadOverWriteSameIndex {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (array, index) = (&terms[0], &terms[1]);
        let aop = array.try_op()?;
        if aop.op != Write || aop[1] != *index {
            return None;
        }
        Some(aop[2].clone())
    }
}

pub(crate) fn read_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    RewritePipeline::new(ctx.level)
        .with_rule(ReadOverWriteSameIndex)
        .apply(terms)
}

struct WriteSameValue;
impl RewriteRule for WriteSameValue {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (array, index, value) = (&terms[0], &terms[1], &terms[2]);
        if is_same_read(value, array, index) {
            Some(array.clone())
        } else {
            None
        }
    }
}

struct WriteConditionalSameValue;
impl RewriteRule for WriteConditionalSameValue {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let (array, index, value) = (&terms[0], &terms[1], &terms[2]);
        let vop = value.try_op()?;
        if vop.op != Ite {
            return None;
        }

        if is_same_read(&vop[1], array, index) {
            return Some(vop[0].ite(array, Term::new_op(Write, [array, index, &vop[2]])));
        }
        if is_same_read(&vop[2], array, index) {
            return Some(vop[0].ite(Term::new_op(Write, [array, index, &vop[1]]), array));
        }

        None
    }
}

pub(crate) fn write_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    RewritePipeline::new(ctx.level)
        .with_rule(WriteSameValue)
        .with_rule(WriteConditionalSameValue)
        .apply(terms)
}

impl FolOp {
    pub fn simplify(self, ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
        // Constant propagation
        if terms.iter().all(|t| t.is_const()) {
            return eval_const_op(self, terms);
        }

        if ctx.level.at_least(OptLevel::O1)
            && let Some(res) = fold_assoc_const_terms(self, terms)
        {
            return Some(res);
        }

        // Idempotent: op(a, a) = a
        if self.traits().contains(OpTrait::Idempotent) && terms[0] == terms[1] {
            return Some(terms[0].clone());
        }

        // Involutive: op(op(a)) = a
        if self.traits().contains(OpTrait::Involutive)
            && let Some(inner_op) = terms[0].try_op()
            && inner_op.op == self
        {
            return Some(inner_op.terms[0].clone());
        }

        op_simplify(self, ctx, terms).or_else(|| {
            if self.traits().contains(OpTrait::Commutative) {
                debug_assert!(terms.len() == 2);
                op_simplify(self, ctx, &[terms[1].clone(), terms[0].clone()])
            } else {
                None
            }
        })
    }
}

fn op_simplify(op: FolOp, ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    match op {
        FolOp::Not => not_simplify(ctx, terms),
        FolOp::And => and_simplify(ctx, terms),
        FolOp::Or => or_simplify(ctx, terms),
        FolOp::Xor => xor_simplify(ctx, terms),
        FolOp::Eq => eq_simplify(ctx, terms),
        FolOp::Ult => ult_simplify(ctx, terms),
        FolOp::Slt => slt_simplify(ctx, terms),
        FolOp::Ite => ite_simplify(ctx, terms),
        FolOp::Concat => concat_simplify(ctx, terms),
        FolOp::Sext => sext_simplify(ctx, terms),
        FolOp::Slice => slice_simplify(ctx, terms),
        FolOp::Add => add_simplify(ctx, terms),
        FolOp::Neg => neg_simplify(ctx, terms),
        FolOp::Mul => mul_simplify(ctx, terms),
        FolOp::Udiv => udiv_simplify(ctx, terms),
        FolOp::Read => read_simplify(ctx, terms),
        FolOp::Write => write_simplify(ctx, terms),
        _ => None,
    }
}

impl Term {
    pub fn simplify(&self, map: &mut GHashMap<Term, Term>) -> Term {
        self.simplify_with_ctx(&SimplifyCtx::default(), map)
    }

    pub fn simplify_with_ctx(&self, ctx: &SimplifyCtx, map: &mut GHashMap<Term, Term>) -> Term {
        if let Some(res) = map.get(self) {
            return res.clone();
        }
        let simp = if let Some(op_term) = self.try_op() {
            let terms: Vec<Term> = op_term
                .terms
                .iter()
                .map(|s| s.simplify_with_ctx(ctx, map))
                .collect();
            if let Some(res) = op_term.op.simplify(ctx, &terms) {
                res.simplify_with_ctx(ctx, map)
            } else {
                Term::new_op(op_term.op, terms)
            }
        } else {
            self.clone()
        };
        map.insert(self.clone(), simp);
        map.get(self).unwrap().clone()
    }
}
