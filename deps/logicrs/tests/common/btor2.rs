//! Minimal BTOR2 writer: prints a term DAG as a combinational BTOR2 model.
//!
//! Variables become `input`s, constants `const`, every core `FolOp` maps to its BTOR2 operator.
//! [`neq_bad_model`] adds `bad = neq(a, b)` so an external checker (`btorsim`, rIC3) can decide
//! whether `a != b` is satisfiable, i.e. whether a rewrite `a -> b` is unsound.
//!
//! Encoding notes (see `src/fol/term.rs`, `src/fol/bitblast.rs`):
//! - `Slice(x, h_dummy, l_dummy)`: the bounds are the *widths* of two dummy constant operands
//!   (inclusive, `h >= l`); BTOR2 is `slice sort x h l`.
//! - `Sext(x, e_dummy)`: the extension width is the width of the dummy operand; BTOR2 `sext sort x e`.
//! - `Concat(hi, lo)`: BTOR2 `concat sort hi lo` (same order).
//! - `Ands`/`Ors` (n-ary) are emitted as chains.
//! - Division by zero: BTOR2 defines `udiv x 0 = ones`, `urem x 0 = x`; logicrs' simulator returns X.

use giputils::bitvec::BitVec;
use logicrs::fol::{FolOp, Sort, Term, TermType};
use std::collections::HashMap;
use std::fmt::Write;

pub struct Btor2Writer {
    out: String,
    next: usize,
    sorts: HashMap<Sort, usize>,
    nodes: HashMap<Term, usize>,
    /// (term, node id, symbol) of every input, in emission order
    pub inputs: Vec<(Term, usize, String)>,
    pub symbols: HashMap<Term, String>,
}

impl Default for Btor2Writer {
    fn default() -> Self {
        Self::new()
    }
}

impl Btor2Writer {
    pub fn new() -> Self {
        Self {
            out: String::new(),
            next: 1,
            sorts: HashMap::new(),
            nodes: HashMap::new(),
            inputs: Vec::new(),
            symbols: HashMap::new(),
        }
    }

    /// Name a variable (used as the `input` symbol).
    pub fn symbol(&mut self, t: &Term, name: impl Into<String>) {
        self.symbols.insert(t.clone(), name.into());
    }

    fn id(&mut self) -> usize {
        let i = self.next;
        self.next += 1;
        i
    }

    pub fn sort(&mut self, s: Sort) -> usize {
        if let Some(&i) = self.sorts.get(&s) {
            return i;
        }
        let i = match s {
            Sort::Bv(w) => {
                assert!(w >= 1, "BTOR2 bitvec sorts must be at least 1 bit wide");
                let i = self.id();
                writeln!(self.out, "{i} sort bitvec {w}").unwrap();
                i
            }
            Sort::Array(iw, ew) => {
                // declare the index and element sorts first: ids must be increasing
                let is = self.sort(Sort::Bv(iw));
                let es = self.sort(Sort::Bv(ew));
                let i = self.id();
                writeln!(self.out, "{i} sort array {is} {es}").unwrap();
                i
            }
        };
        self.sorts.insert(s, i);
        i
    }

    fn bits_msb_first(c: &BitVec) -> String {
        (0..c.len())
            .rev()
            .map(|i| if c.get(i) { '1' } else { '0' })
            .collect()
    }

    fn op_name(op: FolOp) -> &'static str {
        match op {
            FolOp::Not => "not",
            FolOp::And | FolOp::Ands => "and",
            FolOp::Or | FolOp::Ors => "or",
            FolOp::Xor => "xor",
            FolOp::Eq => "eq",
            FolOp::Ult => "ult",
            FolOp::Slt => "slt",
            FolOp::Sll => "sll",
            FolOp::Srl => "srl",
            FolOp::Sra => "sra",
            FolOp::Rol => "rol",
            FolOp::Ror => "ror",
            FolOp::Ite => "ite",
            FolOp::Concat => "concat",
            FolOp::Sext => "sext",
            FolOp::Slice => "slice",
            FolOp::Redxor => "redxor",
            FolOp::Add => "add",
            FolOp::Mul => "mul",
            FolOp::Udiv => "udiv",
            FolOp::Urem => "urem",
            FolOp::Neg => "neg",
            FolOp::Sdiv => "sdiv",
            FolOp::Srem => "srem",
            FolOp::Smod => "smod",
            FolOp::Read => "read",
            FolOp::Write => "write",
            other => panic!("{other:?} is not a core op and never appears in a stored term"),
        }
    }

    /// Emit `t` (and its DAG) and return its node id.
    pub fn node(&mut self, t: &Term) -> usize {
        if let Some(&i) = self.nodes.get(t) {
            return i;
        }
        let sort = self.sort(t.sort());
        let i = match &**t {
            TermType::Const(c) => {
                let i = self.id();
                writeln!(self.out, "{i} const {sort} {}", Self::bits_msb_first(c)).unwrap();
                i
            }
            TermType::Var(_) => {
                let i = self.id();
                let name = self
                    .symbols
                    .get(t)
                    .cloned()
                    .unwrap_or_else(|| format!("v{}", t.id()));
                writeln!(self.out, "{i} input {sort} {name}").unwrap();
                self.inputs.push((t.clone(), i, name));
                i
            }
            TermType::Op(o) => {
                let args: Vec<usize> = match o.op {
                    // the bound/extension dummies are not real operands
                    FolOp::Slice | FolOp::Sext => vec![self.node(&o[0])],
                    _ => o.terms.iter().map(|a| self.node(a)).collect(),
                };
                let name = Self::op_name(o.op);
                match o.op {
                    FolOp::Slice => {
                        let h = o[1].bv_len();
                        let l = o[2].bv_len();
                        let i = self.id();
                        writeln!(self.out, "{i} slice {sort} {} {h} {l}", args[0]).unwrap();
                        i
                    }
                    FolOp::Sext => {
                        let e = o[1].bv_len();
                        let i = self.id();
                        writeln!(self.out, "{i} sext {sort} {} {e}", args[0]).unwrap();
                        i
                    }
                    FolOp::Ands | FolOp::Ors => {
                        let mut acc = args[0];
                        for a in &args[1..] {
                            let i = self.id();
                            writeln!(self.out, "{i} {name} {sort} {acc} {a}").unwrap();
                            acc = i;
                        }
                        acc
                    }
                    _ => {
                        let i = self.id();
                        let a: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                        writeln!(self.out, "{i} {name} {sort} {}", a.join(" ")).unwrap();
                        i
                    }
                }
            }
        };
        self.nodes.insert(t.clone(), i);
        i
    }

    /// Append `bad = neq(a, b)` (works for bit-vector and array sorts).
    pub fn bad_neq(&mut self, a: &Term, b: &Term) {
        let ia = self.node(a);
        let ib = self.node(b);
        let bool_sort = self.sort(Sort::Bv(1));
        let n = self.id();
        writeln!(self.out, "{n} neq {bool_sort} {ia} {ib}").unwrap();
        let bad = self.id();
        writeln!(self.out, "{bad} bad {n}").unwrap();
    }

    pub fn comment(&mut self, s: &str) {
        for line in s.lines() {
            writeln!(self.out, "; {line}").unwrap();
        }
    }

    pub fn finish(self) -> String {
        self.out
    }
}

/// Full model text: inputs for the variables of `a` and `b`, `bad = neq(a, b)`.
pub fn neq_bad_model(a: &Term, b: &Term, header: &str, vars: &[Term]) -> String {
    let mut w = Btor2Writer::new();
    w.comment(header);
    for (k, v) in vars.iter().enumerate() {
        w.symbol(v, format!("x{k}"));
    }
    w.bad_neq(a, b);
    w.finish()
}
