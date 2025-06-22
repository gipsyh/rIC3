#![allow(non_snake_case)]
#![feature(get_mut_unchecked)]

pub mod bmc;
pub mod config;
pub mod frontend;
mod gipsat;
pub mod ic3;
pub mod kind;
pub mod portfolio;
pub mod rlive;
pub mod transys;
pub mod wl;

use config::Config;
use logicrs::{LitVec, Var};
use transys::Transys;

#[derive(Clone, Debug, Default)]
pub struct Witness {
    pub input: Vec<LitVec>,
    pub state: Vec<LitVec>,
}

impl Witness {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.input.len()
    }

    pub fn map_var(&self, f: impl Fn(Var) -> Var) -> Self {
        let input = self.input.iter().map(|w| w.map_var(&f)).collect();
        let state = self.state.iter().map(|w| w.map_var(&f)).collect();
        Self { input, state }
    }

    pub fn filter_map_var(&self, f: impl Fn(Var) -> Option<Var>) -> Self {
        let input = self.input.iter().map(|w| w.filter_map_var(&f)).collect();
        let state = self.state.iter().map(|w| w.filter_map_var(&f)).collect();
        Self { input, state }
    }

    pub fn concat(iter: impl IntoIterator<Item = Witness>) -> Self {
        let mut res = Self::new();
        for witness in iter {
            res.input.extend(witness.input);
            res.state.extend(witness.state);
        }
        res
    }
}

#[derive(Clone, Debug, Default)]
pub struct Proof {
    pub proof: Transys,
}

pub trait Engine {
    fn check(&mut self) -> Option<bool>;

    fn proof(&mut self) -> Proof {
        panic!("unsupport proof");
    }

    fn witness(&mut self) -> Witness {
        panic!("unsupport witness");
    }

    fn statistic(&mut self) {}
}
