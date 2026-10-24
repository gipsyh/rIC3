mod aiger;
pub mod cnf;
mod others;
mod simplify;
mod strash;
mod ternary;

use giputils::{gvec::Gvec, hash::GHashMap};
use logicrs::{Lit, Var};
use std::{
    mem::swap,
    ops::{Index, Range},
    vec,
};
pub use ternary::*;

#[derive(Debug, Clone, Copy)]
pub struct AigLatch {
    pub input: Var,
    pub next: Lit,
    pub init: Option<Lit>,
}

impl AigLatch {
    pub fn new(input: Var, next: Lit, init: Option<Lit>) -> Self {
        Self { input, next, init }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AigNode {
    pub fanin0: Lit,
    pub fanin1: Lit,
}

impl AigNode {
    pub const LEAF: Self = Self {
        fanin0: Lit::NONE,
        fanin1: Lit::NONE,
    };

    #[inline]
    pub fn new_and(mut fanin0: Lit, mut fanin1: Lit) -> Self {
        debug_assert!(!fanin0.is_none() && !fanin1.is_none());
        if fanin0.var() > fanin1.var() {
            swap(&mut fanin0, &mut fanin1);
        }
        Self { fanin0, fanin1 }
    }

    #[inline]
    pub fn is_and(&self) -> bool {
        !self.is_leaf()
    }

    #[inline]
    pub fn is_leaf(&self) -> bool {
        *self == Self::LEAF
    }

    #[inline]
    pub fn fanin0(&self) -> Lit {
        if self.is_and() {
            self.fanin0
        } else {
            panic!("fanin0 called on non-AND node");
        }
    }

    #[inline]
    pub fn fanin1(&self) -> Lit {
        if self.is_and() {
            self.fanin1
        } else {
            panic!("fanin1 called on non-AND node");
        }
    }

    #[inline]
    pub fn fanin(&self) -> (Lit, Lit) {
        if self.is_and() {
            (self.fanin0, self.fanin1)
        } else {
            panic!("fanin called on non-AND node");
        }
    }

    #[inline]
    pub fn set_fanin0(&mut self, fanin: Lit) {
        if self.is_and() {
            self.fanin0 = fanin;
        } else {
            panic!("set_fanin0 called on non-AND node");
        }
    }

    #[inline]
    pub fn set_fanin1(&mut self, fanin: Lit) {
        if self.is_and() {
            self.fanin1 = fanin;
        } else {
            panic!("set_fanin1 called on non-AND node");
        }
    }

    #[inline]
    pub fn map<M>(&self, map: &M) -> Self
    where
        M: Fn(Var) -> Var,
    {
        if self.is_and() {
            Self {
                fanin0: self.fanin0.map_var(map),
                fanin1: self.fanin1.map_var(map),
            }
        } else {
            panic!();
        }
    }
}

#[derive(Debug, Clone)]
pub struct Aig {
    pub nodes: Gvec<AigNode>,
    pub inputs: Vec<Var>,
    pub latchs: Vec<AigLatch>,
    pub outputs: Vec<Lit>,
    pub bads: Vec<Lit>,
    pub constraints: Vec<Lit>,
    pub justice: Vec<Vec<Lit>>,
    pub fairness: Vec<Lit>,
    pub symbols: GHashMap<Var, String>,
}

impl Aig {
    pub fn new() -> Self {
        Self {
            nodes: vec![AigNode::LEAF].into(),
            inputs: Vec::new(),
            latchs: Vec::new(),
            outputs: Vec::new(),
            bads: Vec::new(),
            constraints: Vec::new(),
            justice: Vec::new(),
            fairness: Vec::new(),
            symbols: Default::default(),
        }
    }

    pub fn new_leaf_node(&mut self) -> Var {
        let id = Var::new(self.nodes.len());
        self.nodes.push(AigNode::LEAF);
        id
    }

    #[inline]
    pub fn new_input(&mut self) -> Var {
        let input = self.new_leaf_node();
        self.inputs.push(input);
        input
    }

    #[inline]
    pub fn add_input(&mut self, input: Var) {
        self.inputs.push(input);
    }

    #[inline]
    pub fn new_latch(&mut self, next: Lit, init: Option<Lit>) -> Var {
        let input = self.new_leaf_node();
        self.latchs.push(AigLatch::new(input, next, init));
        input
    }

    #[inline]
    pub fn add_latch(&mut self, input: Var, next: Lit, init: Option<Lit>) {
        self.latchs.push(AigLatch::new(input, next, init))
    }

    #[inline]
    pub fn trivial_new_and_node(&mut self, fanin0: Lit, fanin1: Lit) -> Lit {
        let nodeid = self.nodes.len();
        let and = AigNode::new_and(fanin0, fanin1);
        self.nodes.push(and);
        Var::new(nodeid).lit()
    }

    #[inline]
    pub fn new_and_node(&mut self, mut fanin0: Lit, mut fanin1: Lit) -> Lit {
        if fanin0.var() > fanin1.var() {
            swap(&mut fanin0, &mut fanin1);
        }
        if fanin0 == Lit::constant(true) {
            return fanin1;
        }
        if fanin0 == Lit::constant(false) {
            return Lit::constant(false);
        }
        if fanin1 == Lit::constant(true) {
            return fanin0;
        }
        if fanin1 == Lit::constant(false) {
            return Lit::constant(false);
        }
        if fanin0 == fanin1 {
            fanin0
        } else if fanin0 == !fanin1 {
            Lit::constant(false)
        } else {
            self.trivial_new_and_node(fanin0, fanin1)
        }
    }

    pub fn trivial_new_or_node(&mut self, fanin0: Lit, fanin1: Lit) -> Lit {
        !self.trivial_new_and_node(!fanin0, !fanin1)
    }

    pub fn new_or_node(&mut self, fanin0: Lit, fanin1: Lit) -> Lit {
        !self.new_and_node(!fanin0, !fanin1)
    }

    pub fn trivial_new_ands_node(&mut self, fanin: impl IntoIterator<Item = Lit>) -> Lit {
        let fanin: Vec<_> = fanin.into_iter().collect();
        if fanin.is_empty() {
            Lit::constant(true)
        } else if fanin.len() == 1 {
            fanin[0]
        } else {
            let mut res = self.trivial_new_and_node(fanin[0], fanin[1]);
            for &f in &fanin[2..] {
                res = self.trivial_new_and_node(res, f);
            }
            res
        }
    }

    pub fn new_ands_node(&mut self, fanin: impl IntoIterator<Item = Lit>) -> Lit {
        let fanin: Vec<_> = fanin.into_iter().collect();
        if fanin.is_empty() {
            Lit::constant(true)
        } else if fanin.len() == 1 {
            fanin[0]
        } else {
            let mut res = Lit::constant(true);
            for f in fanin {
                res = self.new_and_node(res, f);
            }
            res
        }
    }

    pub fn trivial_new_ors_node(&mut self, fanin: impl IntoIterator<Item = Lit>) -> Lit {
        !self.trivial_new_ands_node(fanin.into_iter().map(|e| !e))
    }

    pub fn new_ors_node(&mut self, fanin: impl IntoIterator<Item = Lit>) -> Lit {
        !self.new_ands_node(fanin.into_iter().map(|e| !e))
    }

    pub fn new_imply_node(&mut self, fanin0: Lit, fanin1: Lit) -> Lit {
        self.new_or_node(!fanin0, fanin1)
    }

    pub fn new_eq_node(&mut self, fanin0: Lit, fanin1: Lit) -> Lit {
        let x = self.new_and_node(fanin0, fanin1);
        let y = self.new_and_node(!fanin0, !fanin1);
        self.new_or_node(x, y)
    }

    #[inline]
    pub fn get_symbol(&self, v: Var) -> Option<String> {
        self.symbols.get(&v).cloned()
    }

    #[inline]
    pub fn set_symbol(&mut self, v: Var, s: &str) {
        self.symbols.insert(v, s.to_string());
    }
}

impl Aig {
    pub fn num_nodes(&self) -> u32 {
        self.nodes.len() as _
    }

    pub fn nodes_range(&self) -> Range<u32> {
        1..self.num_nodes()
    }

    pub fn nodes_range_with_false(&self) -> Range<u32> {
        0..self.num_nodes()
    }

    pub fn fanin_logic_cone<'a, I: IntoIterator<Item = &'a Lit>>(&self, logic: I) -> Gvec<bool> {
        let mut flag = Gvec::from(vec![false; self.num_nodes() as _]);
        for l in logic {
            flag[*l.var()] = true;
        }
        for id in self.nodes_range_with_false().rev() {
            if flag[id] && self.nodes[id].is_and() {
                flag[*self.nodes[id].fanin0().var()] = true;
                flag[*self.nodes[id].fanin1().var()] = true;
            }
        }
        flag
    }
}

impl Default for Aig {
    fn default() -> Self {
        Self::new()
    }
}

impl Index<usize> for Aig {
    type Output = AigNode;

    fn index(&self, index: usize) -> &Self::Output {
        &self.nodes[index]
    }
}
