pub mod craig;
pub mod itp;
pub mod tracer;

use giputils::{TerminateCtrl, hash::GHashMap};
use logicrs::{Lit, LitVec, Var, satif::Satif};
use std::ffi::{c_int, c_void};

unsafe extern "C" {
    fn cadical_solver_new() -> *mut c_void;
    fn cadical_solver_free(s: *mut c_void);
    fn cadical_solver_reserve(s: *mut c_void, max_var: c_int);
    fn cadical_solver_add_clause(s: *mut c_void, clause: *mut c_int, len: c_int);
    fn cadical_solver_solve(s: *mut c_void, assumps: *mut c_int, len: c_int) -> c_int;
    fn cadical_solver_constrain(s: *mut c_void, constrain: *mut c_int, len: c_int);
    fn cadical_solver_simplify(s: *mut c_void) -> c_int;
    fn cadical_solver_freeze(s: *mut c_void, lit: c_int);
    fn cadical_set_polarity(s: *mut c_void, lit: c_int);
    fn cadical_unset_polarity(s: *mut c_void, lit: c_int);
    fn cadical_solver_model_value(s: *mut c_void, lit: c_int) -> c_int;
    fn cadical_solver_conflict_has(s: *mut c_void, lit: c_int) -> bool;
    fn cadical_solver_clauses(
        s: *mut c_void,
        state: *mut c_void,
        callback: unsafe extern "C" fn(*mut c_void, *const c_int, usize),
    );
    fn cadical_solver_num_clauses(s: *mut c_void) -> usize;
    fn cadical_set_seed(s: *mut c_void, seed: c_int);
    fn cadical_terminate(s: *mut c_void);
}

fn lit_to_cadical_lit(lit: &Lit) -> i32 {
    let mut res = Into::<usize>::into(lit.var()) as i32 + 1;
    if !lit.polarity() {
        res = -res;
    }
    res
}

fn cadical_lit_to_lit(lit: i32) -> Lit {
    let p = lit > 0;
    let v = Var::new(lit.unsigned_abs() as usize - 1);
    Lit::new(v, p)
}

pub struct CaDiCaL {
    solver: *mut c_void,
    num_var: usize,
    tracer_map: GHashMap<*const c_void, *const c_void>,
}

impl CaDiCaL {
    pub fn new() -> Self {
        Self {
            solver: unsafe { cadical_solver_new() },
            num_var: 0,
            tracer_map: GHashMap::default(),
        }
    }
}

impl Satif for CaDiCaL {
    #[inline]
    fn new_var(&mut self) -> Var {
        self.num_var += 1;
        Var::new(self.num_var - 1)
    }

    #[inline]
    fn num_var(&self) -> usize {
        self.num_var
    }

    #[inline]
    fn add_clause(&mut self, clause: &[Lit]) {
        let clause: Vec<i32> = clause.iter().map(lit_to_cadical_lit).collect();
        unsafe { cadical_solver_add_clause(self.solver, clause.as_ptr() as _, clause.len() as _) }
    }

    fn solve(&mut self, assumps: &[Lit]) -> bool {
        let assumps: Vec<i32> = assumps.iter().map(lit_to_cadical_lit).collect();
        match unsafe {
            cadical_solver_solve(self.solver, assumps.as_ptr() as _, assumps.len() as _)
        } {
            10 => true,
            20 => false,
            _ => todo!(),
        }
    }

    fn solve_with_constraint(&mut self, assumps: &[Lit], constraint: Vec<LitVec>) -> bool {
        self.try_solve(assumps, constraint).unwrap()
    }

    fn try_solve(&mut self, assumps: &[Lit], constraint: Vec<LitVec>) -> Option<bool> {
        if constraint.len() > 1 {
            panic!("cadical does not support multiple temporary constraints");
        }
        let assumps: Vec<i32> = assumps.iter().map(lit_to_cadical_lit).collect();
        if !constraint.is_empty() {
            let constraint: Vec<i32> = constraint[0].iter().map(lit_to_cadical_lit).collect();
            unsafe {
                cadical_solver_constrain(
                    self.solver,
                    constraint.as_ptr() as _,
                    constraint.len() as _,
                )
            }
        };
        match unsafe {
            cadical_solver_solve(self.solver, assumps.as_ptr() as _, assumps.len() as _)
        } {
            10 => Some(true),
            20 => Some(false),
            _ => None,
        }
    }

    fn sat_value(&self, lit: Lit) -> Option<bool> {
        let lit = lit_to_cadical_lit(&lit);
        let res = unsafe { cadical_solver_model_value(self.solver, lit) };
        if res == lit {
            Some(true)
        } else if res == -lit {
            Some(false)
        } else {
            None
        }
    }

    fn unsat_has(&self, lit: Lit) -> bool {
        let lit = lit_to_cadical_lit(&lit);
        unsafe { cadical_solver_conflict_has(self.solver, lit) }
    }

    fn simplify(&mut self) -> Option<bool> {
        match unsafe { cadical_solver_simplify(self.solver) } {
            10 => Some(true),
            20 => Some(false),
            _ => None,
        }
    }

    fn set_frozen(&mut self, var: Var, frozen: bool) {
        assert!(frozen);
        unsafe { cadical_solver_freeze(self.solver, lit_to_cadical_lit(&var.lit())) }
    }

    fn clauses(&self) -> Vec<LitVec> {
        unsafe extern "C" fn collect_clause(state: *mut c_void, data: *const c_int, len: usize) {
            // The synchronous traversal lends the clause only for this call.
            // Empty clauses may have a null data pointer, unlike Rust slices.
            let clause = if len == 0 {
                &[]
            } else {
                unsafe { std::slice::from_raw_parts(data, len) }
            };
            let cnf = unsafe { &mut *state.cast::<Vec<LitVec>>() };
            cnf.push(clause.iter().copied().map(cadical_lit_to_lit).collect());
        }
        // Count first to avoid geometric growth of the outer Vec while the
        // solver is still live. Leave one slot for an appended constant unit.
        let count = unsafe { cadical_solver_num_clauses(self.solver) };
        let mut cnf: Vec<LitVec> = Vec::with_capacity(count + 1);
        unsafe {
            cadical_solver_clauses(
                self.solver,
                (&mut cnf as *mut Vec<LitVec>).cast(),
                collect_clause,
            );
        }
        cnf
    }

    fn set_seed(&mut self, seed: u64) {
        unsafe { cadical_set_seed(self.solver, seed as _) }
    }

    fn get_terminate_ctrl(&mut self) -> Box<dyn TerminateCtrl> {
        Box::new(CaDiCaLTerminateCtrl {
            solver: self.solver,
        })
    }
}

impl CaDiCaL {
    /// Initialize variables through `max_var` in one allocation pass. Call
    /// before loading a large CNF to avoid repeatedly growing solver tables.
    /// Like adding clauses, this may invalidate an existing satisfying model.
    pub fn reserve(&mut self, max_var: Var) {
        self.num_var = self.num_var.max(usize::from(max_var) + 1);
        unsafe { cadical_solver_reserve(self.solver, lit_to_cadical_lit(&max_var.lit())) };
    }

    pub fn set_polarity(&mut self, var: Var, pol: Option<bool>) {
        match pol {
            Some(p) => {
                let p = var.lit().not_if(!p);
                unsafe { cadical_set_polarity(self.solver, lit_to_cadical_lit(&p)) }
            }
            None => unsafe { cadical_unset_polarity(self.solver, lit_to_cadical_lit(&var.lit())) },
        };
    }
}

impl Drop for CaDiCaL {
    fn drop(&mut self) {
        unsafe { cadical_solver_free(self.solver) };
    }
}

impl Default for CaDiCaL {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Sync for CaDiCaL {}

unsafe impl Send for CaDiCaL {}

struct CaDiCaLTerminateCtrl {
    solver: *mut c_void,
}

unsafe impl Send for CaDiCaLTerminateCtrl {}
unsafe impl Sync for CaDiCaLTerminateCtrl {}

impl TerminateCtrl for CaDiCaLTerminateCtrl {
    fn terminate(&self) {
        unsafe { cadical_terminate(self.solver) }
    }
}

#[test]
fn test() {
    use logicrs::LitVec;
    let mut solver = CaDiCaL::new();
    let lit0: Lit = solver.new_var().into();
    let lit1: Lit = solver.new_var().into();
    let lit2: Lit = solver.new_var().into();
    solver.add_clause(&LitVec::from([lit0, !lit2]));
    solver.add_clause(&LitVec::from([lit1, !lit2]));
    solver.add_clause(&LitVec::from([!lit0, !lit1, lit2]));
    if solver.solve(&[lit2]) {
        assert!(solver.sat_value(lit0).unwrap());
        assert!(solver.sat_value(lit1).unwrap());
        assert!(solver.sat_value(lit2).unwrap());
    } else {
        panic!()
    }
    assert!(!solver.solve_with_constraint(&[lit2], vec![LitVec::from([!lit0])]));
    assert!(solver.unsat_has(lit2));
}

#[cfg(test)]
mod clause_export_tests {
    use super::*;
    use logicrs::LitVvec;

    #[test]
    fn export_preserves_frozen_projection_and_owns_literals() {
        let (a, b, hidden, output, unit) = (
            Var(0).lit(),
            Var(1).lit(),
            Var(2).lit(),
            Var(3).lit(),
            Var(4).lit(),
        );
        let mut source = LitVvec::cnf_and(hidden, &[a, b]);
        source.extend(LitVvec::cnf_assign(output, !hidden));
        source.push(LitVec::from([!unit]));
        let mut solver = CaDiCaL::new();
        solver.reserve(Var(5));
        assert_eq!(solver.num_var(), 6);
        for clause in source.iter() {
            solver.add_clause(clause);
        }
        let frozen = [a.var(), b.var(), output.var(), unit.var()];
        for &v in &frozen {
            solver.set_frozen(v, true);
        }
        solver.simplify();
        let exported = solver.clauses();
        for _ in 0..3 {
            assert_eq!(solver.clauses(), exported);
        }
        drop(solver);
        let projections = |clauses: &[LitVec]| {
            let mut possible = [false; 16];
            for bits in 0..64 {
                if clauses.iter().all(|c| {
                    c.iter()
                        .any(|l| ((bits & (1 << *l.var())) != 0) == l.polarity())
                }) {
                    let mut projected = 0;
                    for (bit, v) in frozen.iter().enumerate() {
                        projected |= ((bits >> **v) & 1) << bit;
                    }
                    possible[projected] = true;
                }
            }
            possible
        };
        assert_eq!(projections(&source), projections(&exported));
    }

    #[test]
    fn export_empty_formula_and_empty_clause() {
        let mut solver = CaDiCaL::new();
        solver.reserve(Var(0));
        assert!(solver.clauses().is_empty());
        solver.add_clause(&[]);
        assert_eq!(solver.simplify(), Some(false));
        assert_eq!(solver.clauses(), vec![LitVec::new()]);
    }
}
