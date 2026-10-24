use crate::{CaDiCaL, cadical_lit_to_lit};
use logicrs::Lit;
use std::{ffi::c_void, pin::Pin, slice::from_raw_parts};

unsafe extern "C" {
    fn cadical_tracer_new(
        s: *mut c_void,
        t: *mut c_void,
        add_original_clause: *mut c_void,
        add_original_clause: *mut c_void,
        delete_clause: *mut c_void,
        conclude_unsat: *mut c_void,
    ) -> *mut c_void;

    fn cadical_tracer_free(s: *mut c_void, t: *const c_void);
}

#[allow(unused)]
pub trait Tracer {
    fn add_original_clause(&mut self, id: usize, redundant: bool, c: &[Lit], restore: bool) {}

    fn add_derived_clause(&mut self, id: usize, redundant: bool, c: &[Lit], p: &[usize]) {}

    fn delete_clause(&mut self, id: usize, redundant: bool, c: &[Lit]) {}

    fn conclude_unsat(&mut self, conclusion: i32, p: &[usize]) {}
}

impl CaDiCaL {
    pub fn connect_tracer<T: Tracer>(&mut self, tracer: Pin<&T>) {
        let t = tracer.get_ref() as *const T;
        let add_original_clause = add_original_clause::<T>;
        let add_derived_clause = add_derived_clause::<T>;
        let delete_clause = delete_clause::<T>;
        let conclude_unsat = conclude_unsat::<T>;
        let it = unsafe {
            cadical_tracer_new(
                self.solver,
                t as _,
                add_original_clause as _,
                add_derived_clause as _,
                delete_clause as _,
                conclude_unsat as _,
            )
        };
        self.tracer_map.insert(t as *mut c_void, it);
    }

    pub fn disconnect_tracer<T: Tracer>(&mut self, tracer: Pin<&T>) {
        let it = self
            .tracer_map
            .remove(&(tracer.get_ref() as *const T as *const c_void))
            .unwrap();
        unsafe { cadical_tracer_free(self.solver, it) };
    }
}

pub extern "C" fn add_original_clause<T: Tracer>(
    tracer: *mut c_void,
    id: usize,
    redundant: bool,
    c_ptr: *mut c_void,
    c_len: usize,
    restore: bool,
) {
    let tracer = unsafe { &mut *(tracer as *mut T) };
    let c = unsafe { from_raw_parts(c_ptr as *const i32, c_len as _) };
    let c: Vec<Lit> = c.iter().map(|l| cadical_lit_to_lit(*l)).collect();
    tracer.add_original_clause(id, redundant, &c, restore);
}

pub extern "C" fn add_derived_clause<T: Tracer>(
    tracer: *mut c_void,
    id: usize,
    redundant: bool,
    c_ptr: *mut c_void,
    c_len: usize,
    p_ptr: *mut c_void,
    p_len: usize,
) {
    let tracer = unsafe { &mut *(tracer as *mut T) };
    let c = unsafe { from_raw_parts(c_ptr as *const i32, c_len as _) };
    let c: Vec<Lit> = c.iter().map(|l| cadical_lit_to_lit(*l)).collect();
    let p = unsafe { from_raw_parts(p_ptr as *const usize, p_len as _) };
    tracer.add_derived_clause(id, redundant, &c, p);
}

pub extern "C" fn delete_clause<T: Tracer>(
    tracer: *mut c_void,
    id: usize,
    redundant: bool,
    c_ptr: *mut c_void,
    c_len: usize,
) {
    let tracer = unsafe { &mut *(tracer as *mut T) };
    let c = unsafe { from_raw_parts(c_ptr as *const i32, c_len as _) };
    let c: Vec<Lit> = c.iter().map(|l| cadical_lit_to_lit(*l)).collect();
    tracer.delete_clause(id, redundant, &c);
}

pub extern "C" fn conclude_unsat<T: Tracer>(
    tracer: *mut c_void,
    conclusion: i32,
    p_ptr: *mut c_void,
    p_len: usize,
) {
    let tracer = unsafe { &mut *(tracer as *mut T) };
    let p = unsafe { from_raw_parts(p_ptr as *const usize, p_len as _) };
    tracer.conclude_unsat(conclusion, p);
}
