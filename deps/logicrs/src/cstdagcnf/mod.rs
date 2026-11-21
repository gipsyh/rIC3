mod bva;

use crate::{Cnf, DagCnf};
pub use bva::*;
use derive_more::Deref;

#[derive(Debug, Clone, Deref)]
pub struct CstDagCnf {
    #[deref]
    pub dag: DagCnf,
    pub cst: Cnf,
}
