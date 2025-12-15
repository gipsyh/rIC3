mod bitblast;
pub mod certify;
mod preproc;
mod simplify;
pub mod unroll;

use crate::wltransys::certify::Restore;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{Sort, Term, op};
use std::mem::take;

#[derive(Clone, Debug, Default)]
pub struct WlTransys {
    pub input: Vec<Term>,
    pub latch: Vec<Term>,
    pub init: GHashMap<Term, Term>,
    pub next: GHashMap<Term, Term>,
    pub bad: Vec<Term>,
    pub constraint: Vec<Term>,
    pub justice: Vec<Term>,
}

impl WlTransys {
    pub fn print_info(&self) {
        println!("num input: {}", self.input.len());
        println!("num latch: {}", self.latch.len());
        println!("num constraint: {}", self.constraint.len());
    }

    #[inline]
    pub fn init(&self, term: &Term) -> Option<Term> {
        self.init.get(term).cloned()
    }

    #[inline]
    pub fn next(&self, term: &Term) -> Term {
        self.next.get(term).unwrap().clone()
    }

    #[inline]
    pub fn add_input(&mut self, input: &Term) {
        debug_assert!(input.is_var());
        self.input.push(input.clone());
    }

    pub fn add_latch(&mut self, latch: Term, init: Option<Term>, next: Term) {
        debug_assert!(!self.next.contains_key(&latch));
        debug_assert!(latch.is_var());
        self.latch.push(latch.clone());
        if let Some(init) = init {
            self.init.insert(latch.clone(), init);
        }
        self.next.insert(latch, next);
    }

    pub fn remove_no_next_latch(&mut self, rst: &mut Restore) -> GHashSet<Term> {
        let mut no_next = GHashSet::new();
        for l in take(&mut self.latch) {
            if self.next.contains_key(&l) {
                self.latch.push(l.clone());
            } else {
                if let Some(init) = self.init.get(&l).cloned() {
                    if rst.init_var().is_none() {
                        let iv = self.add_init_var();
                        rst.set_init_var(iv);
                    }
                    let iv = rst.init_var().unwrap();
                    self.constraint.push(iv.imply(l.teq(&init)));
                }
                self.init.remove(&l);
                no_next.insert(l.clone());
                self.input.push(l);
            }
        }
        no_next
    }

    pub fn add_init_var(&mut self) -> Term {
        let iv = Term::new_var(Sort::bool());
        self.add_latch(
            iv.clone(),
            Some(Term::bool_const(true)),
            Term::bool_const(false),
        );
        iv
    }

    pub fn compress_bads(&mut self) {
        if self.bad.len() <= 1 {
            return;
        }
        let bad = take(&mut self.bad);
        self.bad = vec![Term::new_op_fold(op::Or, bad)];
    }

    pub fn compress_constraints(&mut self) {
        if self.bad.len() <= 1 {
            return;
        }
        let constraint = take(&mut self.constraint);
        self.constraint = vec![Term::new_op_fold(op::And, constraint)];
    }

    pub fn eliminate_constraint(&mut self) {
        let c = take(&mut self.constraint);
        if c.is_empty() {
            return;
        }
        let c = Term::new_op_fold(op::And, c);
        let v = Term::new_var(Sort::bool());
        let c = v.clone() & c;
        self.add_latch(v.clone(), Some(Term::bool_const(true)), c.clone());
        for i in 0..self.bad.len() {
            self.bad[i] = &self.bad[i] & &c;
        }
    }
}

//     pub fn term_next(&self, term: &Term) -> Term {
//         match term.deref() {
//             TermType::Const(_) => term.clone(),
//             TermType::Var(_) => self.latch_next[term].clone(),
//             TermType::UniOp(op) => {
//                 let a = self.term_next(&op.a);
//                 a.uniop(op.ty)
//             }
//             TermType::BiOp(op) => {
//                 let a = self.term_next(&op.a);
//                 let b = self.term_next(&op.b);
//                 a.biop(&b, op.ty)
//             }
//             TermType::TriOp(_) => todo!(),
//             TermType::ExtOp(op) => {
//                 let a = self.term_next(&op.a);
//                 a.extop(op.ty, op.length)
//             }
//             TermType::SliceOp(op) => {
//                 let a = self.term_next(&op.a);
//                 a.slice(op.upper, op.lower)
//             }
//         }
//     }

//     pub fn term_cube_next(&self, cube: &[Term]) -> TermCube {
//         let mut next = TermCube::new();
//         for l in cube.iter() {
//             next.push(self.term_next(l));
//         }
//         next
//     }
// }
