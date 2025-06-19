mod bitblast;
mod preproc;
mod simplify;

use giputils::hash::GHashMap;
use logicrs::fol::{Term, TermManager};

#[derive(Clone, Debug)]
pub struct WlTransys {
    pub tm: TermManager,
    pub input: Vec<Term>,
    pub latch: Vec<Term>,
    pub init: GHashMap<Term, Term>,
    pub next: GHashMap<Term, Term>,
    pub bad: Term,
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
    pub fn next(&self, term: &Term) -> Term {
        self.next.get(term).unwrap().clone()
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
