use crate::Aig;
use giputils::{
    gvec::Gvec,
    hash::{GHashMap, GHashSet},
};
use logicrs::{Lit, Var};
use std::mem::take;

impl Aig {
    pub fn coi(&self, root: &[Var]) -> GHashSet<Var> {
        let mut latchs = GHashMap::new();
        for l in self.latchs.iter() {
            latchs.insert(l.input, *l);
        }
        let mut refine = GHashSet::new();
        refine.insert(Var::CONST);
        let mut queue = Vec::new();
        for r in root {
            if !refine.contains(r) {
                queue.push(*r);
                refine.insert(*r);
            }
        }
        while let Some(n) = queue.pop() {
            let mut refine_insert = |v: Var| {
                if !refine.contains(&v) {
                    queue.push(v);
                    refine.insert(v);
                }
            };
            if self.nodes[*n].is_and() {
                let fanin0 = self.nodes[*n].fanin0();
                let fanin1 = self.nodes[*n].fanin1();
                refine_insert(fanin0.var());
                refine_insert(fanin1.var());
            } else if let Some(l) = latchs.get(&n) {
                refine_insert(l.next.var());
            }
        }
        refine
    }

    pub fn unroll(&mut self, from: &Aig) {
        let mut next_map = GHashMap::new();
        let false_edge = Lit::constant(false);
        next_map.insert(false_edge.var(), false_edge);
        for l in self.latchs.iter() {
            next_map.insert(l.input, l.next);
        }
        for i in from.nodes_range() {
            let v = Var(i);
            if next_map.contains_key(&v) {
                continue;
            }
            if from.nodes[i].is_and() {
                let fanin0 = self.nodes[i].fanin0();
                let fanin1 = self.nodes[i].fanin1();
                let fanin0 = next_map[&fanin0.var()].not_if(!fanin0.polarity());
                let fanin1 = next_map[&fanin1.var()].not_if(!fanin1.polarity());
                let next = self.new_and_node(fanin0, fanin1);
                next_map.insert(v, next);
            } else {
                let input = self.new_leaf_node();
                self.inputs.push(input);
                let next: Lit = input.into();
                next_map.insert(v, next);
            }
        }
        let edge_map = |e: Lit| next_map[&e.var()].not_if(!e.polarity());
        for (f, s) in from.latchs.iter().zip(self.latchs.iter_mut()) {
            s.next = edge_map(f.next);
        }
        for o in from.outputs.clone() {
            self.outputs.push(edge_map(o));
        }
        for b in from.bads.clone() {
            self.bads.push(edge_map(b));
        }
        for c in from.constraints.clone() {
            self.constraints.push(edge_map(c));
        }
        for j in from.justice.iter() {
            self.justice.push(j.iter().map(|e| edge_map(*e)).collect());
        }
        for f in from.fairness.clone() {
            self.fairness.push(edge_map(f));
        }
    }

    pub fn unroll_to(&self, k: usize) -> Aig {
        let mut res = self.clone();
        for _ in 0..k {
            res.unroll(self);
        }
        res
    }

    pub fn merge(&mut self, other: &Aig) {
        let offset = self.num_nodes() - 1;
        let map = |v: Var| {
            if v.is_constant() { v } else { v + offset }
        };
        for i in 1..other.num_nodes() {
            let n = other.nodes[i].map(&map);
            self.nodes.push(n);
        }
        for i in other.inputs.iter() {
            self.inputs.push(map(*i));
        }
        for l in other.latchs.iter() {
            let mut l = *l;
            l.input = map(l.input);
            l.next = l.next.map_var(map);
            self.latchs.push(l);
        }
        for l in other.outputs.iter() {
            self.outputs.push(l.map_var(map));
        }
        for l in other.bads.iter() {
            self.bads.push(l.map_var(map));
        }
        for l in other.constraints.iter() {
            self.constraints.push(l.map_var(map));
        }
        for j in other.justice.iter() {
            self.justice
                .push(j.iter().map(|e| e.map_var(map)).collect());
        }
        for l in other.fairness.iter() {
            self.fairness.push(l.map_var(map));
        }
    }

    pub fn reencode(&self) -> Self {
        let mut res = Self::new();
        let mut encode_map = Gvec::new();
        encode_map.reserve(self.nodes.len());
        encode_map[*Var::CONST] = Var::CONST;
        let mut max_id = 0;
        for &l in self.inputs.iter() {
            max_id += 1;
            encode_map[*l] = Var::new(max_id);
        }
        for l in self.latchs.iter() {
            max_id += 1;
            encode_map[*l.input] = Var::new(max_id);
        }
        for i in 0..self.nodes.len() {
            if self.nodes[i].is_and() {
                max_id += 1;
                encode_map[i] = Var::new(max_id);
            }
        }
        assert!(max_id + 1 == self.nodes.len());
        let edge_map = |e: Lit| e.map_var(|v| encode_map[*v]);
        for &l in self.inputs.iter() {
            assert!(res.new_input() == encode_map[*l]);
        }
        for l in self.latchs.iter() {
            assert!(res.new_latch(edge_map(l.next), l.init) == encode_map[*l.input]);
        }
        for i in 1..self.nodes.len() {
            if self.nodes[i].is_and() {
                let fanin0 = edge_map(self.nodes[i].fanin0());
                let fanin1 = edge_map(self.nodes[i].fanin1());
                let nl = res.trivial_new_and_node(fanin0, fanin1).var();
                assert!(encode_map[i] == nl);
            }
        }
        res.outputs = self.outputs.iter().map(|e| edge_map(*e)).collect();
        res.bads = self.bads.iter().map(|e| edge_map(*e)).collect();
        res.constraints = self.constraints.iter().map(|e| edge_map(*e)).collect();
        res.justice = self
            .justice
            .iter()
            .map(|j| j.iter().map(|e| edge_map(*e)).collect())
            .collect();
        res.fairness = self.fairness.iter().map(|e| edge_map(*e)).collect();
        res.symbols = self
            .symbols
            .iter()
            .map(|(&v, s)| (encode_map[*v], s.clone()))
            .collect();
        assert!(res.nodes.len() == self.nodes.len());
        res
    }

    pub fn aig_move(&self) -> Self {
        let mut res = self.clone();
        let latch = res.new_leaf_node();
        let constrains = res.new_ands_node(res.constraints.clone());
        let next = res.new_and_node(latch.into(), constrains);
        res.add_latch(latch, next, Some(Lit::constant(true)));
        if !res.bads.is_empty() {
            res.bads[0] = res.new_and_node(next, res.bads[0]);
        }
        if !res.outputs.is_empty() {
            res.outputs[0] = res.new_and_node(next, res.outputs[0]);
        }
        res.constraints.clear();
        res
    }

    pub fn compress_property(&mut self) -> Vec<Lit> {
        let b = take(&mut self.bads);
        let p = self.new_ors_node(b.clone());
        self.bads.push(p);
        b
    }

    pub fn gate_init_to_constraint(&mut self) {
        let mut gate_init = Vec::new();
        for l in self.latchs.iter_mut() {
            if let Some(init) = l.init
                && !init.var().is_constant()
            {
                gate_init.push((l.input, init));
                l.init = None;
            }
        }
        if gate_init.is_empty() {
            return;
        }
        let init: Lit = self
            .new_latch(Lit::constant(false), Some(Lit::constant(true)))
            .into();
        for (l, gi) in gate_init {
            let l = l.lit();
            let eq = self.new_eq_node(l, gi);
            let init_eq = self.new_imply_node(init, eq);
            self.constraints.push(init_eq);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Aig;
    use logicrs::Lit;

    #[test]
    fn reencode_keeps_constant_literals() {
        // One latch with the constant 0 as its next state, bad = the latch.
        let a = Aig::read_aiger(b"aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let r = a.reencode();
        assert_eq!(r.latchs.len(), 1);
        assert_eq!(r.latchs[0].next, Lit::constant(false));
        assert_eq!(r.bads, vec![r.latchs[0].input.lit()]);
        assert_eq!(r.to_string(), "aag 1 0 1 0 0 1\n2 0\n2\n");
        let mut bytes = Vec::new();
        r.write_aiger(&mut bytes, false).unwrap();
        let back = Aig::read_aiger(&bytes).unwrap();
        assert_eq!(back.latchs[0].next, Lit::constant(false));

        // The constant 1 as a next state, an AND fanin and an output.
        let a = Aig::read_aiger(b"aag 3 1 1 1 1 1\n2\n4 1\n1\n6\n6 2 1\n").unwrap();
        let r = a.reencode();
        assert_eq!(r.latchs[0].next, Lit::constant(true));
        assert_eq!(r.outputs, vec![Lit::constant(true)]);
        assert_eq!(r.nodes[3usize].fanin(), a.nodes[3usize].fanin());
        assert_eq!(r.to_string(), a.to_string());
    }
}
