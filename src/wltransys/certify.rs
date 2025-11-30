use crate::wltransys::WlTransys;
use giputils::hash::GHashMap;
use logicrs::{
    Var,
    fol::{Term, Value},
};

#[derive(Clone, Debug, Default)]
pub struct WlWitness {
    pub input: GHashMap<Term, Value>,
    pub state: GHashMap<Term, Value>,
}

impl WlWitness {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Clone, Debug, Default)]
pub struct WlProof {
    pub proof: WlTransys,
}

#[derive(Clone, Default)]
pub struct Restore {
    pub bb_rst: GHashMap<Var, (Term, usize)>,
    init_var: Option<Term>,
}

impl Restore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn init_var(&self) -> Option<Term> {
        self.init_var.clone()
    }

    pub fn set_init_var(&mut self, iv: Term) {
        assert!(self.init_var.is_none());
        self.init_var = Some(iv);
    }
}
