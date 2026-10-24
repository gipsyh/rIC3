use crate::{Lit, LitVec, Var};
use giputils::TerminateCtrl;
use std::{sync::mpsc::channel, thread::scope, time::Duration};

pub trait Satif: Send {
    fn new_var(&mut self) -> Var;

    fn new_var_to(&mut self, var: Var) {
        while Var::new(self.num_var()) <= var {
            self.new_var();
        }
    }

    fn num_var(&self) -> usize;

    #[inline]
    fn max_var(&self) -> Var {
        Var(self.num_var() as u32 - 1)
    }

    fn add_clause(&mut self, clause: &[Lit]);

    fn solve(&mut self, assumps: &[Lit]) -> bool;

    fn solve_with_constraint(&mut self, _assumps: &[Lit], _constraint: Vec<LitVec>) -> bool {
        panic!("unsupport solve with constraint");
    }

    /// Maybe return unknown results
    fn try_solve(&mut self, _assumps: &[Lit], _constraint: Vec<LitVec>) -> Option<bool> {
        panic!("unsupport try_solve");
    }

    fn solve_with_limit(
        &mut self,
        assumps: &[Lit],
        constraint: Vec<LitVec>,
        limit: Duration,
    ) -> Option<bool> {
        let stop = self.get_terminate_ctrl();
        let (tx, rx) = channel();
        scope(|s| {
            let join = s.spawn(|| tx.send(self.try_solve(assumps, constraint)).unwrap());
            match rx.recv_timeout(limit) {
                Ok(Some(x)) => Some(x),
                Ok(None) => unreachable!(),
                Err(_) => {
                    stop.terminate();
                    join.join().unwrap();
                    None
                }
            }
        })
    }

    fn sat_value(&self, lit: Lit) -> Option<bool>;

    #[inline]
    fn sat_value_lit(&self, var: Var) -> Option<Lit> {
        self.sat_value(var.lit()).map(|v| Lit::new(var, v))
    }

    fn unsat_has(&self, _lit: Lit) -> bool {
        panic!("unsupport assumption");
    }

    fn simplify(&mut self) -> Option<bool> {
        panic!("unsupport simplify");
    }

    fn set_frozen(&mut self, _var: Var, _frozen: bool) {
        panic!("unsupport set frozen");
    }

    fn clauses(&self) -> Vec<LitVec> {
        panic!("unsupport get clauses");
    }

    fn set_seed(&mut self, _seed: u64) {
        panic!("unsupport set seed");
    }

    fn flip_to_none(&mut self, _var: Var) -> bool {
        false
    }

    fn get_terminate_ctrl(&mut self) -> Box<dyn TerminateCtrl> {
        panic!("unsupport get_terminate_ctrl");
    }
}
