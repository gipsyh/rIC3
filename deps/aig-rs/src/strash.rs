use crate::Aig;
use giputils::hash::GHashMap;
use logicrs::{Lit, Var};
use std::mem::swap;

impl Aig {
    pub fn strash(&self) -> Self {
        let mut map: GHashMap<(Lit, Lit), Var> = GHashMap::new();
        let mut strash_map: GHashMap<Var, Var> = GHashMap::new();
        for (id, node) in self.nodes.iter().enumerate() {
            if node.is_and() {
                let mut fanin0 = node.fanin0();
                if let Some(eq) = strash_map.get(&fanin0.var()) {
                    fanin0 = Lit::from(*eq).not_if(!fanin0.polarity());
                }
                let mut fanin1 = node.fanin1();
                if let Some(eq) = strash_map.get(&fanin1.var()) {
                    fanin1 = Lit::from(*eq).not_if(!fanin1.polarity());
                }
                if fanin0.var() > fanin1.var() {
                    swap(&mut fanin0, &mut fanin1);
                }
                match map.get(&(fanin0, fanin1)) {
                    Some(eq) => {
                        strash_map.insert(Var::new(id), *eq);
                    }
                    None => {
                        map.insert((fanin0, fanin1), Var::new(id));
                    }
                }
            }
        }
        println!("{:?}", strash_map.len());
        println!("{:?}", map.len());
        todo!()
    }
}
