use super::{Term, TermType};
use std::ops::Deref;

impl Term {
    pub fn replace(&self, x: &Term, y: &Term) -> Term {
        if self.eq(x) {
            return y.clone();
        }
        let TermType::Op(op) = self.deref() else {
            return self.clone();
        };
        let terms: Vec<_> = op.terms.iter().map(|t| t.replace(x, y)).collect();
        Term::new_op(op.op, &terms)
    }
}
