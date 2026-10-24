use crate::{CaDiCaL, cadical_lit_to_lit};
use logicrs::{LitVec, Var};
use std::{ffi::c_int, os::raw::c_void};

unsafe extern "C" {
    fn cadical_craig_new(s: *mut c_void) -> *mut c_void;
    fn cadical_craig_free(s: *mut c_void, c: *mut c_void);
    fn cadical_craig_label_var(c: *mut c_void, var: i32, t: u8);
    fn cadical_craig_label_clause(c: *mut c_void, id: i32, t: u8);
    fn cadical_craig_create_craig_interpolant(
        c: *mut c_void,
        next_var: *mut c_int,
        len: *mut c_int,
    ) -> *mut c_void;
}

#[derive(Clone, Copy)]
pub enum VarLabel {
    A,
    B,
    Global,
}

impl From<VarLabel> for u8 {
    fn from(val: VarLabel) -> Self {
        match val {
            VarLabel::A => 0,
            VarLabel::B => 1,
            VarLabel::Global => 2,
        }
    }
}

#[derive(Clone, Copy)]
pub enum ClauseLabel {
    A,
    B,
}

impl From<ClauseLabel> for u8 {
    fn from(val: ClauseLabel) -> Self {
        match val {
            ClauseLabel::A => 0,
            ClauseLabel::B => 1,
        }
    }
}

pub struct Craig {
    solver: *mut c_void,
    craig: *mut c_void,
    num_clause: usize,
}

impl Craig {
    pub fn new(solver: &mut CaDiCaL) -> Self {
        let craig = unsafe { cadical_craig_new(solver.solver) };
        Self {
            solver: solver.solver,
            craig,
            num_clause: 0,
        }
    }

    pub fn label_var(&mut self, var: Var, label: VarLabel) {
        let mut var: i32 = var.into();
        var += 1;
        unsafe { cadical_craig_label_var(self.craig, var, label.into()) }
    }

    pub fn label_clause(&mut self, label: ClauseLabel) {
        self.num_clause += 1;
        unsafe { cadical_craig_label_clause(self.craig, self.num_clause as _, label.into()) }
    }

    pub fn interpolant(&mut self, next_var: usize) -> Vec<LitVec> {
        unsafe {
            let mut cnf = Vec::new();
            let mut len = 0;
            let mut next_var = next_var as i32;
            next_var += 1;
            let clauses: *mut usize = cadical_craig_create_craig_interpolant(
                self.craig,
                &mut next_var as *mut _,
                &mut len as *mut _,
            ) as _;
            let clauses = Vec::from_raw_parts(clauses, len as _, len as _);
            for i in (0..clauses.len()).step_by(2) {
                let data = clauses[i] as *mut i32;
                let len = clauses[i + 1];
                let cls: Vec<i32> = Vec::from_raw_parts(data, len, len);
                cnf.push(LitVec::from_iter(cls.into_iter().map(cadical_lit_to_lit)));
            }
            cnf
        }
    }
}

impl Drop for Craig {
    fn drop(&mut self) {
        unsafe { cadical_craig_free(self.solver, self.craig) }
    }
}

#[test]
fn test() {
    use logicrs::{Lit, satif::Satif};
    let mut solver = CaDiCaL::new();
    let mut craig = Craig::new(&mut solver);
    craig.label_var(Var::new(1), VarLabel::Global);
    craig.label_var(Var::new(2), VarLabel::Global);
    craig.label_clause(ClauseLabel::A);
    solver.add_clause(&[Lit::new(Var(0), true), Lit::new(Var(1), false)]);
    craig.label_clause(ClauseLabel::A);
    solver.add_clause(&[Lit::new(Var(0), false), Lit::new(Var(2), false)]);
    craig.label_clause(ClauseLabel::A);
    solver.add_clause(&[Lit::new(Var(1), true)]);
    craig.label_clause(ClauseLabel::B);
    solver.add_clause(&[Lit::new(Var(1), false), Lit::new(Var(2), true)]);
    craig.label_clause(ClauseLabel::B);
    solver.add_clause(&[Lit::new(Var(1), true), Lit::new(Var(3), true)]);
    craig.label_clause(ClauseLabel::B);
    solver.add_clause(&[Lit::new(Var(3), false)]);
    dbg!(solver.solve(&[]));
    dbg!(craig.interpolant(4));
}
