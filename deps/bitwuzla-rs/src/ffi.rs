use giputils::{bitvec::BitVec, hash::GHashMap};
use logicrs::fol::{FolOp, OpTerm, Sort, Term, TermType};
use std::ffi::{CString, c_void};

use crate::{ops::BitwuzlaOp, option};

unsafe extern "C" {
    fn bitwuzla_term_manager_new() -> *mut c_void;
    fn bitwuzla_term_manager_delete(tm: *mut c_void);
    fn bitwuzla_options_new() -> *mut c_void;
    fn bitwuzla_options_delete(op: *mut c_void);
    fn bitwuzla_new(pm: *mut c_void, op: *mut c_void) -> *mut c_void;
    fn bitwuzla_delete(b: *mut c_void);
    fn bitwuzla_mk_bv_sort(tm: *mut c_void, size: u64) -> *mut c_void;
    fn bitwuzla_mk_const(tm: *mut c_void, sort: *mut c_void, symbol: *const i8) -> *mut c_void;
    fn bitwuzla_mk_bv_value(
        tm: *mut c_void,
        sort: *mut c_void,
        value: *const i8,
        base: u8,
    ) -> *mut c_void;
    fn bitwuzla_mk_bv_value_uint64(tm: *mut c_void, sort: *mut c_void, value: u64) -> *mut c_void;
    fn bitwuzla_mk_term(
        tm: *mut c_void,
        kind: u32,
        argc: u32,
        args: *const *mut c_void,
    ) -> *mut c_void;
    fn bitwuzla_mk_term1_indexed2(
        tm: *mut c_void,
        kind: u32,
        arg: *mut c_void,
        idx0: u64,
        idx1: u64,
    ) -> *mut c_void;
    fn bitwuzla_mk_term1_indexed1(
        tm: *mut c_void,
        kind: u32,
        arg: *mut c_void,
        idx0: u64,
    ) -> *mut c_void;
    fn bitwuzla_assert(bitwuzla: *mut c_void, term: *mut c_void);
    fn bitwuzla_check_sat(bitwuzla: *mut c_void) -> u32;
    fn bitwuzla_check_sat_assuming(
        bitwuzla: *mut c_void,
        argc: u32,
        args: *const *mut c_void,
    ) -> u32;
    fn bitwuzla_get_unsat_assumptions(
        bitwuzla: *mut c_void,
        size: *mut usize,
    ) -> *const *mut c_void;
    fn bitwuzla_get_unsat_core(bitwuzla: *mut c_void, size: *mut usize) -> *const *mut c_void;
    fn bitwuzla_push(bitwuzla: *mut c_void, nlevels: u64);
    fn bitwuzla_pop(bitwuzla: *mut c_void, nlevels: u64);
    fn bitwuzla_get_value(bitwuzla: *mut c_void, term: *mut c_void) -> *mut c_void;
    fn bitwuzla_term_value_get_str(term: *mut c_void) -> *const i8;
    fn bitwuzla_term_is_value(term: *mut c_void) -> bool;
    fn bitwuzla_set_option(op: *mut c_void, option: u32, val: u64);
}

pub struct Bitwuzla {
    tm: *mut c_void,
    op: *mut c_void,
    bitwuzla: *mut c_void,
    term_map: GHashMap<Term, *mut c_void>,
    rev_term_map: GHashMap<*mut c_void, Term>,
    bv1_one: *mut c_void,
    bv1_zero: *mut c_void,
    bv2bool: GHashMap<*mut c_void, *mut c_void>,
    bool2bv: GHashMap<*mut c_void, *mut c_void>,
}

impl Bitwuzla {
    #[inline]
    fn bv1_to_bool(&mut self, bv1: *mut c_void) -> *mut c_void {
        if let Some(r) = self.bv2bool.get(&bv1) {
            return *r;
        }
        let r = unsafe {
            bitwuzla_mk_term(
                self.tm,
                BitwuzlaOp::Equal as u32,
                2,
                [bv1, self.bv1_one].as_ptr(),
            )
        };
        self.bv2bool.insert(bv1, r);
        self.bool2bv.insert(r, bv1);
        r
    }

    fn bool_to_bv1(&mut self, b: *mut c_void) -> *mut c_void {
        if let Some(r) = self.bool2bv.get(&b) {
            return *r;
        }
        let r = unsafe {
            bitwuzla_mk_term(
                self.tm,
                BitwuzlaOp::Ite as u32,
                3,
                [b, self.bv1_one, self.bv1_zero].as_ptr(),
            )
        };
        self.bv2bool.insert(r, b);
        self.bool2bv.insert(b, r);
        r
    }

    fn convert_sort(&self, sort: Sort) -> *mut c_void {
        match sort {
            Sort::Bv(w) => unsafe { bitwuzla_mk_bv_sort(self.tm, w as u64) },
            _ => todo!("unsupport other sorts"),
        }
    }

    fn convert_term(&mut self, term: &Term) -> *mut c_void {
        if let Some(&t) = self.term_map.get(term) {
            return t;
        }

        let res = match &**term {
            TermType::Const(c) => self.convert_const(c, term.sort()),
            TermType::Var(id) => self.convert_var(*id, term.sort()),
            TermType::Op(op) => self.convert_op(op),
        };

        self.term_map.insert(term.clone(), res);
        self.rev_term_map.insert(res, term.clone());
        res
    }

    fn restore_term(&self, term: *mut c_void) -> Option<Term> {
        self.rev_term_map.get(&term).cloned().or_else(|| {
            self.bool2bv
                .get(&term)
                .and_then(|t| self.rev_term_map.get(t).cloned())
        })
    }

    fn convert_const(&self, c: &BitVec, sort: Sort) -> *mut c_void {
        let sort_ptr = self.convert_sort(sort);
        let s = format!("{}", c);
        let c_str = CString::new(s).unwrap();
        unsafe { bitwuzla_mk_bv_value(self.tm, sort_ptr, c_str.as_ptr(), 2) }
    }

    fn convert_var(&self, _id: usize, sort: Sort) -> *mut c_void {
        let sort_ptr = self.convert_sort(sort);
        unsafe { bitwuzla_mk_const(self.tm, sort_ptr, std::ptr::null()) }
    }

    fn convert_op(&mut self, op_term: &OpTerm) -> *mut c_void {
        if op_term.op == FolOp::Slice {
            let arg = self.convert_term(&op_term.terms[0]);
            let h = op_term.terms[1].bv_len() as u64;
            let l = op_term.terms[2].bv_len() as u64;
            return unsafe {
                bitwuzla_mk_term1_indexed2(self.tm, BitwuzlaOp::BvExtract as u32, arg, h, l)
            };
        } else if op_term.op == FolOp::Sext {
            let arg = self.convert_term(&op_term.terms[0]);
            let w = op_term.terms[1].bv_len() as u64;
            return unsafe {
                bitwuzla_mk_term1_indexed1(self.tm, BitwuzlaOp::BvSignExtend as u32, arg, w)
            };
        } else if op_term.op == FolOp::Uext {
            let arg = self.convert_term(&op_term.terms[0]);
            let w = op_term.terms[1].bv_len() as u64;
            return unsafe {
                bitwuzla_mk_term1_indexed1(self.tm, BitwuzlaOp::BvZeroExtend as u32, arg, w)
            };
        }

        let mut args: Vec<*mut c_void> =
            op_term.terms.iter().map(|t| self.convert_term(t)).collect();

        if op_term.op == FolOp::Ite {
            args[0] = self.bv1_to_bool(args[0]);
        }
        if op_term.op == FolOp::Implies {
            args[0] = self.bv1_to_bool(args[0]);
            args[1] = self.bv1_to_bool(args[1]);
        }

        let kind = op_term.op.into();

        let res =
            unsafe { bitwuzla_mk_term(self.tm, kind as u32, args.len() as u32, args.as_ptr()) };

        match kind {
            BitwuzlaOp::Equal
            | BitwuzlaOp::Distinct
            | BitwuzlaOp::BvUlt
            | BitwuzlaOp::BvUgt
            | BitwuzlaOp::BvSlt
            | BitwuzlaOp::BvSgt => self.bool_to_bv1(res),
            _ => res,
        }
    }
}

impl Bitwuzla {
    pub fn new() -> Self {
        let tm = unsafe { bitwuzla_term_manager_new() };
        let op = unsafe { bitwuzla_options_new() };
        unsafe { bitwuzla_set_option(op, option::BitwuzlaOption::ProduceModels as u32, 1) };
        unsafe {
            bitwuzla_set_option(
                op,
                option::BitwuzlaOption::ProduceUnsatAssumptions as u32,
                1,
            )
        };
        unsafe { bitwuzla_set_option(op, option::BitwuzlaOption::ProduceUnsatCores as u32, 1) };
        let bitwuzla = unsafe { bitwuzla_new(tm, op) };

        let bv1_sort = unsafe { bitwuzla_mk_bv_sort(tm, 1) };
        let bv1_one = unsafe { bitwuzla_mk_bv_value_uint64(tm, bv1_sort, 1) };
        let bv1_zero = unsafe { bitwuzla_mk_bv_value_uint64(tm, bv1_sort, 0) };

        Self {
            tm,
            op,
            bitwuzla,
            term_map: GHashMap::new(),
            rev_term_map: GHashMap::new(),
            bv1_one,
            bv1_zero,
            bv2bool: GHashMap::new(),
            bool2bv: GHashMap::new(),
        }
    }

    pub fn assert(&mut self, t: &Term) {
        let term = self.convert_term(t);
        let term = self.bv1_to_bool(term);
        unsafe { bitwuzla_assert(self.bitwuzla, term) }
    }

    pub fn solve<'a>(&mut self, assumps: impl IntoIterator<Item = &'a Term>) -> bool {
        let assumps: Vec<*mut c_void> = assumps
            .into_iter()
            .map(|t| {
                debug_assert!(t.is_bool());
                let term = self.convert_term(t);
                self.bv1_to_bool(term)
            })
            .collect();
        let res = if assumps.is_empty() {
            unsafe { bitwuzla_check_sat(self.bitwuzla) }
        } else {
            unsafe {
                bitwuzla_check_sat_assuming(self.bitwuzla, assumps.len() as u32, assumps.as_ptr())
            }
        };
        res == 10
    }

    pub fn push(&mut self, nlevels: usize) {
        unsafe { bitwuzla_push(self.bitwuzla, nlevels as _) }
    }

    pub fn pop(&mut self, nlevels: usize) {
        unsafe { bitwuzla_pop(self.bitwuzla, nlevels as _) }
    }

    pub fn sat_value(&mut self, term: &Term) -> Option<BitVec> {
        let t = self.convert_term(term);
        let val = unsafe { bitwuzla_get_value(self.bitwuzla, t) };
        debug_assert!(unsafe { bitwuzla_term_is_value(val) });
        let s_ptr = unsafe { bitwuzla_term_value_get_str(val) };
        let s = unsafe { std::ffi::CStr::from_ptr(s_ptr).to_string_lossy() };
        let bits: Vec<bool> = s.chars().rev().map(|c| c == '1').collect();
        Some(BitVec::from(&bits))
    }

    pub fn unsat_assump(&self) -> Vec<Term> {
        let mut size = 0;
        let data = unsafe { bitwuzla_get_unsat_assumptions(self.bitwuzla, &mut size) };
        let data = unsafe { std::slice::from_raw_parts(data, size) };
        data.iter().filter_map(|&t| self.restore_term(t)).collect()
    }

    pub fn unsat_core(&self) -> Vec<Term> {
        let mut size = 0;
        let data = unsafe { bitwuzla_get_unsat_core(self.bitwuzla, &mut size) };
        let data = unsafe { std::slice::from_raw_parts(data, size) };
        data.iter().filter_map(|&t| self.restore_term(t)).collect()
    }
}

impl Drop for Bitwuzla {
    fn drop(&mut self) {
        unsafe { bitwuzla_delete(self.bitwuzla) }
        unsafe { bitwuzla_term_manager_delete(self.tm) }
        unsafe { bitwuzla_options_delete(self.op) }
    }
}

impl Default for Bitwuzla {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Sync for Bitwuzla {}
unsafe impl Send for Bitwuzla {}
