use super::term::Term;
use crate::fol::Sort;
use crate::{DagCnf, Lit, LitVvec};
use std::fmt::{self, Display};

/// MLIR-style operation trait metadata (commutative, associative, ...).
#[enumflags2::bitflags]
#[repr(u32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OpTrait {
    /// Commutative: `a op b == b op a`.
    Commutative = 1 << 0,
    /// Associative: `(a op b) op c == a op (b op c)`.
    Associative = 1 << 1,
    /// Idempotent: `a op a == a`.
    Idempotent = 1 << 2,
    /// Involutive: applying the operation twice returns the original value.
    Involutive = 1 << 3,
}

pub type OpTraitSet = enumflags2::BitFlags<OpTrait>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FolOp {
    Not,
    And,
    Ands,
    Or,
    Ors,
    Xor,
    Eq,
    Ult,
    Slt,
    Sll,
    Srl,
    Sra,
    Rol,
    Ror,
    Ite,
    Concat,
    Sext,
    Slice,
    Redxor,
    Add,
    Sub,
    Mul,
    Udiv,
    Urem,
    Neg,
    Sdiv,
    Srem,
    Smod,
    Read,
    Write,
    Inc,
    Dec,
    Nand,
    Nor,
    Xnor,
    Iff,
    Implies,
    Redand,
    Redor,
    Udivo,
    Neq,
    Uext,
    Ugt,
    Ulte,
    Ugte,
    Sgt,
    Slte,
    Sgte,
}

pub use FolOp::*;

impl Display for FolOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl FolOp {
    #[inline]
    pub fn is_core(&self) -> bool {
        matches!(
            self,
            FolOp::Not
                | FolOp::And
                | FolOp::Ands
                | FolOp::Or
                | FolOp::Ors
                | FolOp::Xor
                | FolOp::Eq
                | FolOp::Ult
                | FolOp::Slt
                | FolOp::Sll
                | FolOp::Srl
                | FolOp::Sra
                | FolOp::Rol
                | FolOp::Ror
                | FolOp::Ite
                | FolOp::Concat
                | FolOp::Sext
                | FolOp::Slice
                | FolOp::Redxor
                | FolOp::Add
                | FolOp::Mul
                | FolOp::Udiv
                | FolOp::Urem
                | FolOp::Neg
                | FolOp::Sdiv
                | FolOp::Srem
                | FolOp::Smod
                | FolOp::Read
                | FolOp::Write
        )
    }

    pub fn num_operand(&self) -> usize {
        match self {
            FolOp::Not
            | FolOp::Redxor
            | FolOp::Neg
            | FolOp::Inc
            | FolOp::Dec
            | FolOp::Redand
            | FolOp::Redor => 1,
            FolOp::And
            | FolOp::Or
            | FolOp::Xor
            | FolOp::Eq
            | FolOp::Ult
            | FolOp::Slt
            | FolOp::Sll
            | FolOp::Srl
            | FolOp::Sra
            | FolOp::Rol
            | FolOp::Ror
            | FolOp::Concat
            | FolOp::Sext
            | FolOp::Add
            | FolOp::Sub
            | FolOp::Mul
            | FolOp::Udiv
            | FolOp::Urem
            | FolOp::Sdiv
            | FolOp::Srem
            | FolOp::Smod
            | FolOp::Read
            | FolOp::Nand
            | FolOp::Nor
            | FolOp::Xnor
            | FolOp::Iff
            | FolOp::Implies
            | FolOp::Udivo
            | FolOp::Neq
            | FolOp::Uext
            | FolOp::Ugt
            | FolOp::Ulte
            | FolOp::Ugte
            | FolOp::Sgt
            | FolOp::Slte
            | FolOp::Sgte => 2,
            FolOp::Ite | FolOp::Slice | FolOp::Write => 3,
            FolOp::Ands | FolOp::Ors => panic!("fold op has no num_operand"),
        }
    }

    #[inline]
    pub fn sort(&self, terms: &[Term]) -> Sort {
        match self {
            FolOp::Not
            | FolOp::And
            | FolOp::Or
            | FolOp::Xor
            | FolOp::Sll
            | FolOp::Srl
            | FolOp::Sra
            | FolOp::Rol
            | FolOp::Ror
            | FolOp::Add
            | FolOp::Sub
            | FolOp::Mul
            | FolOp::Udiv
            | FolOp::Urem
            | FolOp::Neg
            | FolOp::Sdiv
            | FolOp::Srem
            | FolOp::Smod
            | FolOp::Write => terms[0].sort(),
            FolOp::Redxor | FolOp::Eq | FolOp::Ors | FolOp::Ands | FolOp::Ult | FolOp::Slt => {
                Sort::Bv(1)
            }
            FolOp::Ite => terms[1].sort(),
            FolOp::Concat | FolOp::Sext => Sort::Bv(terms[0].bv_len() + terms[1].bv_len()),
            FolOp::Slice => Sort::Bv(terms[1].bv_len() - terms[2].bv_len() + 1),
            FolOp::Read => {
                let (_, e) = terms[0].sort().array();
                Sort::Bv(e)
            }
            _ => {
                if !self.is_core() {
                    panic!("{:?} not support sort", self);
                } else {
                    terms[0].sort()
                }
            }
        }
    }

    pub fn normalize(&self, terms: &[Term]) -> Term {
        match self {
            FolOp::Inc => &terms[0] + terms[0].mk_bv_const_one(),
            FolOp::Dec => &terms[0] - terms[0].mk_bv_const_one(),
            FolOp::Nand => !(&terms[0] & &terms[1]),
            FolOp::Nor => !(&terms[0] | &terms[1]),
            FolOp::Xnor => !Term::new_op(Xor, terms),
            FolOp::Iff => terms[0].op1(Eq, &terms[1]),
            FolOp::Implies => !&terms[0] | &terms[1],
            FolOp::Redand => {
                let ones = terms[0].mk_bv_const_ones();
                terms[0].op1(Eq, &ones)
            }
            FolOp::Redor => {
                let zero = terms[0].mk_bv_const_zero();
                !terms[0].op1(Eq, &zero)
            }
            FolOp::Sub => terms[0].op1(Add, terms[1].op0(Neg)),
            FolOp::Udivo => {
                let zero = terms[1].mk_bv_const_zero();
                !terms[1].op1(Eq, &zero)
            }
            FolOp::Neq => !Term::new_op(Eq, terms),
            FolOp::Uext => {
                if terms[1].bv_len() == 0 {
                    terms[0].clone()
                } else {
                    Term::new_op(Concat, &[terms[1].clone(), terms[0].clone()])
                }
            }
            FolOp::Ugt => terms[1].op1(Ult, &terms[0]),
            FolOp::Ulte => !terms[1].op1(Ult, &terms[0]),
            FolOp::Ugte => !Term::new_op(Ult, terms),
            FolOp::Sgt => terms[1].op1(Slt, &terms[0]),
            FolOp::Slte => !terms[1].op1(Slt, &terms[0]),
            FolOp::Sgte => !Term::new_op(Slt, terms),
            _ => panic!("{:?} not support normalize", self),
        }
    }

    #[inline]
    pub fn traits(&self) -> OpTraitSet {
        match self {
            FolOp::Not | FolOp::Neg => OpTrait::Involutive.into(),
            FolOp::And | FolOp::Or => {
                OpTrait::Commutative | OpTrait::Associative | OpTrait::Idempotent
            }
            FolOp::Xor | FolOp::Add | FolOp::Mul => OpTrait::Commutative | OpTrait::Associative,
            FolOp::Eq => OpTrait::Commutative.into(),
            _ => OpTraitSet::empty(),
        }
    }

    pub fn cnf_encode(&self, dc: &mut DagCnf, terms: &[Lit]) -> Lit {
        match self {
            FolOp::Not => !terms[0],
            FolOp::And | FolOp::Ands => {
                let l = dc.new_var().lit();
                dc.add_rel(l.var(), &LitVvec::cnf_and(l, terms));
                l
            }
            FolOp::Or | FolOp::Ors => {
                let l = dc.new_var().lit();
                dc.add_rel(l.var(), &LitVvec::cnf_or(l, terms));
                l
            }
            FolOp::Xor => {
                let l = dc.new_var().lit();
                dc.add_rel(l.var(), &LitVvec::cnf_xor(l, terms[0], terms[1]));
                l
            }
            FolOp::Eq => {
                let l = dc.new_var().lit();
                dc.add_rel(l.var(), &LitVvec::cnf_xnor(l, terms[0], terms[1]));
                l
            }
            FolOp::Ite => {
                let l = dc.new_var().lit();
                dc.add_rel(l.var(), &LitVvec::cnf_ite(l, terms[0], terms[1], terms[2]));
                l
            }
            _ => panic!("{:?} not support cnf_encode", self),
        }
    }
}

impl From<&str> for FolOp {
    #[inline]
    fn from(value: &str) -> Self {
        match value.to_lowercase().as_str() {
            "not" => FolOp::Not,
            "and" => FolOp::And,
            "ands" => FolOp::Ands,
            "or" => FolOp::Or,
            "ors" => FolOp::Ors,
            "xor" => FolOp::Xor,
            "eq" => FolOp::Eq,
            "ult" => FolOp::Ult,
            "slt" => FolOp::Slt,
            "sll" => FolOp::Sll,
            "srl" => FolOp::Srl,
            "sra" => FolOp::Sra,
            "rol" => FolOp::Rol,
            "ror" => FolOp::Ror,
            "ite" => FolOp::Ite,
            "concat" => FolOp::Concat,
            "sext" => FolOp::Sext,
            "slice" => FolOp::Slice,
            "redxor" => FolOp::Redxor,
            "add" => FolOp::Add,
            "sub" => FolOp::Sub,
            "mul" => FolOp::Mul,
            "udiv" => FolOp::Udiv,
            "urem" => FolOp::Urem,
            "neg" => FolOp::Neg,
            "sdiv" => FolOp::Sdiv,
            "srem" => FolOp::Srem,
            "smod" => FolOp::Smod,
            "read" => FolOp::Read,
            "write" => FolOp::Write,
            "inc" => FolOp::Inc,
            "dec" => FolOp::Dec,
            "nand" => FolOp::Nand,
            "nor" => FolOp::Nor,
            "xnor" => FolOp::Xnor,
            "iff" => FolOp::Iff,
            "implies" => FolOp::Implies,
            "redand" => FolOp::Redand,
            "redor" => FolOp::Redor,
            "udivo" => FolOp::Udivo,
            "neq" => FolOp::Neq,
            "uext" => FolOp::Uext,
            "ugt" => FolOp::Ugt,
            "ulte" => FolOp::Ulte,
            "ugte" => FolOp::Ugte,
            "sgt" => FolOp::Sgt,
            "slte" => FolOp::Slte,
            "sgte" => FolOp::Sgte,
            _ => panic!("unsupport {} op!", value),
        }
    }
}
