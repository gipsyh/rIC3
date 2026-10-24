use giputils::bitvec::BitVec;
use logicrs::fol::Term;

pub struct Bitwuzla;

impl Bitwuzla {
    pub fn new() -> Self {
        panic!(
            "Bitwuzla library not found. Please install bitwuzla: https://github.com/bitwuzla/bitwuzla"
        );
    }

    pub fn assert(&mut self, _t: &Term) {
        unreachable!()
    }

    pub fn solve<'a>(&mut self, _assumps: impl IntoIterator<Item = &'a Term>) -> bool {
        unreachable!()
    }

    pub fn push(&mut self, _nlevels: usize) {
        unreachable!()
    }

    pub fn pop(&mut self, _nlevels: usize) {
        unreachable!()
    }

    pub fn sat_value(&mut self, _term: &Term) -> Option<BitVec> {
        unreachable!()
    }

    pub fn unsat_assump(&self) -> Vec<Term> {
        unreachable!()
    }

    pub fn unsat_core(&self) -> Vec<Term> {
        unreachable!()
    }
}

impl Default for Bitwuzla {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Sync for Bitwuzla {}
unsafe impl Send for Bitwuzla {}
