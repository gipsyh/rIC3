mod bva;

use crate::{Cnf, DagCnf};
pub use bva::*;
use std::ops::Deref;

#[derive(Debug, Clone)]
pub struct CstDagCnf {
    pub dag: DagCnf,
    pub cst: Cnf,
}

impl Deref for CstDagCnf {
    type Target = DagCnf;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.dag
    }
}
