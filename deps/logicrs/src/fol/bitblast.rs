use super::op::*;
use super::{Sort, Term, TermType, TermVec};
use crate::{DagCnf, Lit};
use giputils::{bitvec::BitVec, hash::GHashMap};
use std::{iter::repeat_with, ops::Deref, slice};

#[inline]
fn bv_const_bitblast(c: &BitVec) -> TermVec {
    c.iter().map(Term::bool_const).collect()
}

#[inline]
fn bv_const_cnf_encode(c: &BitVec) -> Lit {
    debug_assert!(c.len() == 1);
    Lit::constant(c.get(0))
}

pub fn var_bitblast(sort: Sort) -> TermVec {
    let size = sort.size();
    repeat_with(|| Term::new_var(Sort::bool()))
        .take(size)
        .collect()
}

impl Term {
    pub fn bitblast(&self, map: &mut GHashMap<Term, TermVec>) -> TermVec {
        if let Some(res) = map.get(self) {
            return res.clone();
        }
        let blast = match self.deref() {
            TermType::Const(const_term) => bv_const_bitblast(const_term),
            TermType::Var(_) => var_bitblast(self.sort()),
            TermType::Op(op_term) => {
                let terms: Vec<TermVec> = op_term.terms.iter().map(|s| s.bitblast(map)).collect();
                op_term.op.bitblast(&terms)
            }
        };
        map.insert(self.clone(), blast.clone());
        map.get(self).unwrap().clone()
    }

    pub fn cnf_encode(&self, dc: &mut DagCnf, map: &mut GHashMap<Term, Lit>) -> Lit {
        if let Some(res) = map.get(self) {
            return *res;
        }
        let blast = match self.deref() {
            TermType::Const(const_term) => bv_const_cnf_encode(const_term),
            TermType::Var(_) => dc.new_var().lit(),
            TermType::Op(op_term) => {
                let terms: Vec<Lit> = op_term
                    .terms
                    .iter()
                    .map(|s| s.cnf_encode(dc, map))
                    .collect();
                op_term.op.cnf_encode(dc, &terms)
            }
        };
        map.insert(self.clone(), blast);
        *map.get(self).unwrap()
    }
}

pub fn bitblast_terms<I: IntoIterator<Item = impl AsRef<Term>>>(
    terms: I,
    map: &mut GHashMap<Term, TermVec>,
) -> impl Iterator<Item = TermVec> {
    terms.into_iter().map(|t| t.as_ref().bitblast(map))
}

pub fn cnf_encode_terms<I: IntoIterator<Item = impl AsRef<Term>>>(
    terms: I,
    dc: &mut DagCnf,
    map: &mut GHashMap<Term, Lit>,
) -> impl Iterator<Item = Lit> {
    terms.into_iter().map(|t| t.as_ref().cnf_encode(dc, map))
}

pub(crate) fn not_bitblast(terms: &[TermVec]) -> TermVec {
    terms[0].iter().map(|t| !t).collect()
}

pub(crate) fn and_bitblast(terms: &[TermVec]) -> TermVec {
    Term::new_op_elementwise(And, &terms[0], &terms[1])
}

pub(crate) fn or_bitblast(terms: &[TermVec]) -> TermVec {
    Term::new_op_elementwise(Or, &terms[0], &terms[1])
}

pub(crate) fn xor_bitblast(terms: &[TermVec]) -> TermVec {
    Term::new_op_elementwise(Xor, &terms[0], &terms[1])
}

pub(crate) fn eq_bitblast(terms: &[TermVec]) -> TermVec {
    let neqs = Term::new_op_elementwise(Eq, &terms[0], &terms[1]);
    TermVec::from([Term::new_op(Ands, &neqs)])
}

pub(crate) fn ult_bitblast(terms: &[TermVec]) -> TermVec {
    let mut res = Term::bool_const(false);
    for (x, y) in terms[0].iter().zip(terms[1].iter()) {
        res = (!x & y) | ((!x | y) & res)
    }
    TermVec::from([res])
}

pub(crate) fn slt_bitblast(terms: &[TermVec]) -> TermVec {
    let x = &terms[0];
    let y = &terms[1];
    let len = x.len();
    let (xr, xs) = (&x[..len - 1], &x[len - 1]);
    let (yr, ys) = (&y[..len - 1], &y[len - 1]);
    let ls = xs & !ys;
    let eqs = xs.op1(Eq, ys);
    let mut el = Term::bool_const(false);
    for (x, y) in xr.iter().zip(yr.iter()) {
        el = (!x & y) | ((!x | y) & el)
    }
    TermVec::from([ls | (eqs & el)])
}

pub(crate) fn sll_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    assert!(x.len() == y.len());
    if terms[0].len() == 1 {
        return TermVec::from([&x[0] & !&y[0]]);
    }
    let width = x.len();
    // ceil(log2(width))
    let stages = (usize::BITS - (width - 1).leading_zeros()) as usize;
    let mut res = x.clone();
    for shift_bit in 0..stages {
        let shift_step = 1 << shift_bit;
        let shift = &y[shift_bit];
        let mut nres = TermVec::new();
        for j in 0..shift_step.min(width) {
            nres.push(&!shift & &res[j]);
        }
        for j in shift_step..width {
            nres.push(Term::new_op(Ite, [shift, &res[j - shift_step], &res[j]]));
        }
        res = nres;
    }

    if stages < width {
        let no_toobig = !Term::new_op(Ors, &y[stages..]);
        res = res
            .into_iter()
            .map(|b| Term::new_op(And, [&no_toobig, &b]))
            .collect();
    }
    res
}

pub(crate) fn srl_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    assert!(x.len() == y.len());
    if terms[0].len() == 1 {
        return TermVec::from([&x[0] & !&y[0]]);
    }
    let width = x.len();
    let stages = (usize::BITS - (width - 1).leading_zeros()) as usize;
    let mut res = x.clone();
    for shift_bit in 0..stages {
        let shift_step = 1 << shift_bit;
        let shift = &y[shift_bit];
        let mut nres = TermVec::new();
        let c = width.saturating_sub(shift_step);
        for j in 0..c {
            nres.push(Term::new_op(Ite, [shift, &res[j + shift_step], &res[j]]));
        }
        for j in c..width {
            nres.push(&!shift & &res[j]);
        }
        res = nres;
    }

    if stages < width {
        let not_toobig = !Term::new_op(Ors, &y[stages..]);
        res = res
            .into_iter()
            .map(|b| Term::new_op(And, [&not_toobig, &b]))
            .collect();
    }
    res
}

pub(crate) fn sra_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    assert!(x.len() == y.len());
    if terms[0].len() == 1 {
        return x.clone();
    }
    let width = x.len();
    let stages = (usize::BITS - (width - 1).leading_zeros()) as usize;
    let mut res = x.clone();
    for shift_bit in 0..stages {
        let shift_step = 1 << shift_bit;
        let c = width.saturating_sub(shift_step);
        let shift = &y[shift_bit];
        let mut nres = TermVec::new();
        for j in 0..c {
            nres.push(Term::new_op(Ite, [shift, &res[j + shift_step], &res[j]]));
        }
        for j in c..width {
            nres.push(Term::new_op(Ite, [shift, &res[width - 1], &res[j]]));
        }
        res = nres;
    }

    if stages < width {
        let not_toobig = !Term::new_op(Ors, &y[stages..]);
        let sign = res[width - 1].clone();
        res = res
            .into_iter()
            .map(|b| Term::new_op(Ite, [&not_toobig, &b, &sign]))
            .collect();
    }
    res
}

/// Barrel rotation: bit `i` of the amount rotates by `2^i mod width`. The step of every stage is
/// computed by doubling modulo `width`, so no `1 << i` can overflow and every bit of the amount
/// is honoured for any width (rotation by `y` equals rotation by `y mod width`).
fn rotate_bitblast(x: &TermVec, y: &TermVec, left: bool) -> TermVec {
    assert_eq!(x.len(), y.len());
    let width = x.len();
    // width = 1: rotation is a no-op
    if width == 1 {
        return x.clone();
    }
    let mut res = x.clone();
    let mut step = 1 % width;
    for shift in y.iter() {
        if step != 0 {
            let mut next = TermVec::new();
            for j in 0..width {
                let src = if left {
                    (j + width - step) % width
                } else {
                    (j + step) % width
                };
                next.push(Term::new_op(Ite, [shift, &res[src], &res[j]]));
            }
            res = next;
        }
        step = (step * 2) % width;
    }
    res
}

pub(crate) fn rol_bitblast(terms: &[TermVec]) -> TermVec {
    rotate_bitblast(&terms[0], &terms[1], true)
}

pub(crate) fn ror_bitblast(terms: &[TermVec]) -> TermVec {
    rotate_bitblast(&terms[0], &terms[1], false)
}

pub(crate) fn ite_bitblast(terms: &[TermVec]) -> TermVec {
    let mut res = TermVec::new();
    for (x, y) in terms[1].iter().zip(terms[2].iter()) {
        res.push(terms[0][0].op2(Ite, x, y));
    }
    res
}

pub(crate) fn concat_bitblast(terms: &[TermVec]) -> TermVec {
    let mut res = terms[1].clone();
    res.extend_from_slice(&terms[0]);
    res
}

pub(crate) fn sext_bitblast(terms: &[TermVec]) -> TermVec {
    let x = &terms[0];
    let mut res = x.clone();
    let ext = vec![x[x.len() - 1].clone(); terms[1].len()];
    res.extend(ext);
    res
}

pub(crate) fn slice_bitblast(terms: &[TermVec]) -> TermVec {
    let l = terms[2].len();
    let h = terms[1].len();
    terms[0][l..=h].iter().cloned().collect()
}

pub(crate) fn redxor_bitblast(terms: &[TermVec]) -> TermVec {
    TermVec::from([Term::new_op_fold(Xor, terms[0].iter())])
}

#[inline]
pub(crate) fn full_adder(x: &Term, y: &Term, c: &Term) -> (Term, Term) {
    let r = Term::new_op_fold(Xor, [x, y, c]);
    let xy = x & y;
    let xc = x & c;
    let yc = y & c;
    let c = Term::new_op(Ors, [&xy, &xc, &yc]);
    (r, c)
}

pub(crate) fn add_bitblast(terms: &[TermVec]) -> TermVec {
    let mut r;
    let mut c = Term::bool_const(false);
    let mut res = TermVec::new();
    for (x, y) in terms[0].iter().zip(terms[1].iter()) {
        (r, c) = full_adder(x, y, &c);
        res.push(r);
    }
    res
}

pub(crate) fn mul_bitblast(terms: &[TermVec]) -> TermVec {
    let x = &terms[0];
    let y = &terms[1];
    assert!(x.len() == y.len());
    let len = x.len();
    let mut res: TermVec = x.iter().map(|t| t & &y[0]).collect();
    for i in 1..len {
        let mut c = Term::bool_const(false);
        for j in i..len {
            let add = &y[i] & &x[j - i];
            (res[j], c) = full_adder(&res[j], &add, &c);
        }
    }
    res
}

fn scgate_co(r: &Term, d: &Term, ci: &Term) -> Term {
    let d_or_ci = d | ci;
    let d_and_ci = d & ci;
    let m = &d_or_ci & r;
    d_and_ci | &m
}

fn scgate_s(r: &Term, d: &Term, ci: &Term, q: &Term) -> Term {
    let d_or_ci = d | ci;
    let d_and_ci = d & ci;
    let t1 = &d_or_ci & !&d_and_ci;
    let t2 = &t1 & q;
    let t2_or_r = &t2 | r;
    let t2_and_r = &t2 & r;
    &t2_or_r & !&t2_and_r
}

fn udiv_urem_bitblast(a: &TermVec, din: &TermVec) -> (TermVec, TermVec) {
    let nd: Vec<Term> = din.iter().map(|t| !t).collect();
    let size = a.len();
    let mut s = vec![vec![Term::bool_const(false); size + 1]; size + 1];
    let mut c = vec![vec![Term::bool_const(false); size + 1]; size + 1];
    let mut q = TermVec::new();

    for j in 0..size {
        c[j][0] = Term::bool_const(true);
        s[j][0] = a[size - j - 1].clone();
        for (i, ndi) in nd.iter().enumerate().take(size) {
            c[j][i + 1] = scgate_co(&s[j][i], ndi, &c[j][i]);
        }
        q.push(&c[j][size] | &s[j][size]);
        for (i, ndi) in nd.iter().enumerate().take(size) {
            s[j + 1][i + 1] = scgate_s(&s[j][i], ndi, &c[j][i], &q[j]);
        }
    }
    q.reverse(); // quotients come MSB first
    (q, TermVec::from(s[size][1..=size].to_vec()))
}

pub(crate) fn udiv_bitblast(terms: &[TermVec]) -> TermVec {
    let (q, _) = udiv_urem_bitblast(&terms[0], &terms[1]);
    q
}

pub(crate) fn urem_bitblast(terms: &[TermVec]) -> TermVec {
    let (_, r) = udiv_urem_bitblast(&terms[0], &terms[1]);
    r
}

pub(crate) fn neg_bitblast(terms: &[TermVec]) -> TermVec {
    let x = &terms[0];
    let mut res = TermVec::new();
    res.push(x[0].clone());
    let mut c = !&x[0];
    for i in 1..x.len() {
        res.push((&c & &x[i]) | (!&c & !&x[i]));
        c = &c & !&x[i];
    }
    res
}

pub(crate) fn sdiv_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    let w = x.len();
    if w == 1 {
        return TermVec::from([!(!&x[0] & &y[0])]);
    }
    let (sgnx, sgny) = (x.last().unwrap(), y.last().unwrap());
    let xor = sgnx ^ sgny;
    let negx = neg_bitblast(terms);
    let negy = neg_bitblast(&terms[1..]);
    let cndx = negx
        .iter()
        .zip(x.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgnx, n, p]))
        .collect();
    let cndy = negy
        .iter()
        .zip(y.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgny, n, p]))
        .collect();
    let udiv = udiv_bitblast(&[cndx, cndy]);
    let neg_udiv = neg_bitblast(slice::from_ref(&udiv));
    neg_udiv
        .iter()
        .zip(udiv.iter())
        .map(|(n, p)| Term::new_op(Ite, [&xor, n, p]))
        .collect()
}

pub(crate) fn srem_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    let w = x.len();
    if w == 1 {
        return TermVec::from([&x[0] & !&y[0]]);
    }
    let (sgnx, sgny) = (x.last().unwrap(), y.last().unwrap());
    let negx = neg_bitblast(terms);
    let negy = neg_bitblast(&terms[1..]);
    let cndx = negx
        .iter()
        .zip(x.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgnx, n, p]))
        .collect();
    let cndy = negy
        .iter()
        .zip(y.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgny, n, p]))
        .collect();
    let urem = urem_bitblast(&[cndx, cndy]);
    let neg_urem = neg_bitblast(slice::from_ref(&urem));
    neg_urem
        .iter()
        .zip(urem.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgnx, n, p]))
        .collect()
}

pub(crate) fn smod_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    let w = x.len();
    if w == 1 {
        return TermVec::from([&x[0] & !&y[0]]);
    }
    let (sgnx, sgny) = (x.last().unwrap(), y.last().unwrap());
    let negx = neg_bitblast(terms);
    let negy = neg_bitblast(&terms[1..]);
    let cndx = negx
        .iter()
        .zip(x.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgnx, n, p]))
        .collect();
    let cndy = negy
        .iter()
        .zip(y.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgny, n, p]))
        .collect();
    let posi_urem = urem_bitblast(&[cndx, cndy]);
    let nega_urem = neg_bitblast(slice::from_ref(&posi_urem));
    let nega_urem_add = add_bitblast(&[nega_urem.clone(), y.clone()]);
    let posi_urem_add = add_bitblast(&[posi_urem.clone(), y.clone()]);
    let urem_is0 = Term::new_op(Ands, posi_urem.iter().map(|t| !t));

    let both_posi = !sgnx & !sgny;
    let nega_posi = sgnx & !sgny;
    let posi_nega = !sgnx & sgny;
    let posi_nega = posi_urem_add
        .iter()
        .zip(nega_urem.iter())
        .map(|(a, b)| Term::new_op(Ite, [&posi_nega, a, b]));
    let nega_posi = nega_urem_add
        .iter()
        .zip(posi_nega)
        .map(|(a, b)| Term::new_op(Ite, [&nega_posi, a, &b]));
    let both_posi = &urem_is0 | &both_posi;
    let both_posi = posi_urem
        .iter()
        .zip(nega_posi)
        .map(|(a, b)| Term::new_op(Ite, [&both_posi, a, &b]));
    both_posi.collect()
}

fn onehot_rec(idx: usize, x: &[Term], res: &mut [Term]) {
    let len = 1_usize.checked_shl(idx as u32).unwrap();
    debug_assert!(res.len() == len.checked_mul(2).unwrap());
    res[0] = &res[0] & !&x[idx];
    for i in 0..len {
        res[i] = res[0].clone();
    }
    res[len] = &res[len] & &x[idx];
    for i in len..res.len() {
        res[i] = res[len].clone();
    }
    if idx == 0 {
        return;
    }
    onehot_rec(idx - 1, x, &mut res[0..len]);
    onehot_rec(idx - 1, x, &mut res[len..]);
}

fn onehot_encode(x: &[Term]) -> TermVec {
    let len = 1_usize.checked_shl(x.len() as u32).unwrap();
    let mut res = vec![Term::bool_const(true); len];
    onehot_rec(x.len() - 1, x, &mut res);
    TermVec::from(res)
}

pub(crate) fn read_bitblast(terms: &[TermVec]) -> TermVec {
    let (array, index) = (&terms[0], &terms[1]);
    let index_len = index.len();
    let array_len = array.len();
    let index_range = 1_usize.checked_shl(index_len as u32).unwrap();
    let element_len = array_len / index_range;
    let onehot = onehot_encode(index);
    let mut res = TermVec::new();
    for i in 0..element_len {
        let mut r = Term::bool_const(false);
        for j in 0..index_range {
            r = onehot[j].ite(&array[element_len * j + i], &r);
        }
        res.push(r);
    }
    res
}

pub(crate) fn write_bitblast(terms: &[TermVec]) -> TermVec {
    let (array, index, value) = (&terms[0], &terms[1], &terms[2]);
    let index_len = index.len();
    let array_len = array.len();
    let index_range = 1_usize.checked_shl(index_len as u32).unwrap();
    let element_len = array_len / index_range;
    let onehot = onehot_encode(index);
    let mut res = array.clone();
    for i in 0..element_len {
        for j in 0..index_range {
            let r = &mut res[element_len * j + i];
            *r = onehot[j].ite(&value[i], &r);
        }
    }
    res
}

impl FolOp {
    pub fn bitblast(&self, terms: &[TermVec]) -> TermVec {
        match self {
            FolOp::Not => not_bitblast(terms),
            FolOp::And => and_bitblast(terms),
            FolOp::Or => or_bitblast(terms),
            FolOp::Xor => xor_bitblast(terms),
            FolOp::Eq => eq_bitblast(terms),
            FolOp::Ult => ult_bitblast(terms),
            FolOp::Slt => slt_bitblast(terms),
            FolOp::Sll => sll_bitblast(terms),
            FolOp::Srl => srl_bitblast(terms),
            FolOp::Sra => sra_bitblast(terms),
            FolOp::Rol => rol_bitblast(terms),
            FolOp::Ror => ror_bitblast(terms),
            FolOp::Ite => ite_bitblast(terms),
            FolOp::Concat => concat_bitblast(terms),
            FolOp::Sext => sext_bitblast(terms),
            FolOp::Slice => slice_bitblast(terms),
            FolOp::Redxor => redxor_bitblast(terms),
            FolOp::Add => add_bitblast(terms),
            FolOp::Mul => mul_bitblast(terms),
            FolOp::Udiv => udiv_bitblast(terms),
            FolOp::Urem => urem_bitblast(terms),
            FolOp::Neg => neg_bitblast(terms),
            FolOp::Sdiv => sdiv_bitblast(terms),
            FolOp::Srem => srem_bitblast(terms),
            FolOp::Smod => smod_bitblast(terms),
            FolOp::Read => read_bitblast(terms),
            FolOp::Write => write_bitblast(terms),
            _ => panic!("{:?} not support biblast", self),
        }
    }
}
