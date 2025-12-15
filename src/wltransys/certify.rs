use std::ops::{Deref, DerefMut};

use crate::wltransys::WlTransys;
use giputils::hash::GHashMap;
use logicrs::{
    Var,
    fol::{BvTermValue, Term, TermValue},
};

#[derive(Clone, Debug, Default)]
pub struct WlWitness {
    pub input: Vec<Vec<BvTermValue>>,
    pub state: Vec<Vec<TermValue>>,
    pub bad_id: usize,
}

impl WlWitness {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.state.len()
    }

    pub fn resize(&mut self, size: usize) {
        self.input.resize(size, Vec::new());
        self.state.resize(size, Vec::new());
    }
}

#[derive(Clone, Debug, Default)]
pub struct WlProof {
    pub proof: WlTransys,
}

impl Deref for WlProof {
    type Target = WlTransys;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.proof
    }
}

impl DerefMut for WlProof {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.proof
    }
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
