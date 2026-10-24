use crate::Aig;
use giputils::gvec::Gvec;
use logicrs::{Lbool, Lit};

impl Aig {
    pub fn ternary_simulate(&self, input: &[Lbool], state: &[Lbool]) -> Gvec<Lbool> {
        assert!(input.len() == self.inputs.len());
        assert!(state.len() == self.latchs.len());
        let mut ans = Gvec::from(vec![Lbool::default(); self.nodes.len()]);
        ans[0] = Lbool::FALSE;
        for i in 0..self.inputs.len() {
            ans[*self.inputs[i]] = input[i];
        }
        for i in 0..self.latchs.len() {
            ans[*self.latchs[i].input] = state[i];
        }
        for i in self.nodes_range() {
            if self.nodes[i].is_and() {
                let fanin0 =
                    ans[*self.nodes[i].fanin0().var()].not_if(!self.nodes[i].fanin0().polarity());
                let fanin1 =
                    ans[*self.nodes[i].fanin1().var()].not_if(!self.nodes[i].fanin1().polarity());
                ans[i] = fanin0 & fanin1;
            }
        }
        ans
    }
}

pub struct TernarySimulate<'a> {
    aig: &'a Aig,
    state: Vec<Lbool>,
    value: Gvec<Lbool>,
}

impl<'a> TernarySimulate<'a> {
    pub fn new(aig: &'a Aig, state: Vec<Lbool>) -> Self {
        assert!(state.len() == aig.latchs.len());
        Self {
            aig,
            state,
            value: Default::default(),
        }
    }

    pub fn simulate(&mut self, input: Vec<Lbool>) {
        self.value = self.aig.ternary_simulate(&input, &self.state);
        for i in 0..self.aig.latchs.len() {
            let ln = self.aig.latchs[i].next;
            self.state[i] = self.value[*ln.var()].not_if(!ln.polarity());
        }
    }

    pub fn value(&self, e: Lit) -> Lbool {
        self.value[*e.var()].not_if(!e.polarity())
    }
}
