use crate::{Aig, AigNode};
use giputils::{gvec::Gvec, hash::GHashMap};
use logicrs::{Lit, Var, VarMap};
use std::mem::take;

impl Aig {
    /// Simplify combinational logic without renumbering inputs or latches.
    /// Aliases (including complemented aliases) are propagated to all fanins
    /// and roots. Obsolete gates are left for reachability-based CNF encoding
    /// to discard; no sequential assumptions or constraints are used.
    pub fn comb_simplify(&mut self) {
        let mut map: Gvec<Lit> = (0..self.num_nodes()).map(|i| Lit::from(Var(i))).collect();
        let mut unique = GHashMap::new();
        for i in self.nodes_range() {
            if !self.nodes[i].is_and() {
                continue;
            }
            let (a, b) = self.nodes[i].fanin();
            let a = map[*a.var()].not_if(!a.polarity());
            let b = map[*b.var()].not_if(!b.polarity());
            let (a, b) = self.simplify_and_fanins(a, b);
            self.nodes[i] = AigNode::new_and(a, b);
            if a == b {
                map[i] = a;
                continue;
            }
            if let Some((_, t, e)) = self.is_ite(Var(i))
                && t == e
            {
                // ITE(c, t, t) = t, even when t is complemented.
                map[i] = t;
                continue;
            }
            let key = self.nodes[i].fanin();
            map[i] = *unique.entry(key).or_insert(Lit::from(Var(i)));
        }
        let remap = |e: &mut Lit| *e = map[*e.var()].not_if(!e.polarity());
        for latch in &mut self.latchs {
            remap(&mut latch.next);
            if let Some(init) = &mut latch.init {
                remap(init);
            }
        }
        for edge in self
            .outputs
            .iter_mut()
            .chain(self.bads.iter_mut())
            .chain(self.constraints.iter_mut())
            .chain(self.justice.iter_mut().flatten())
            .chain(self.fairness.iter_mut())
        {
            remap(edge);
        }
    }

    // Return (x, x) for an alias, otherwise a reduced pair of AND fanins.
    fn simplify_and_fanins(&self, mut a: Lit, mut b: Lit) -> (Lit, Lit) {
        loop {
            if a.is_constant(false) || b.is_constant(false) || a == !b {
                let f = Lit::constant(false);
                return (f, f);
            }
            if a.is_constant(true) || a == b {
                return (b, b);
            }
            if b.is_constant(true) {
                return (a, a);
            }
            let mut reduced = None;
            for (outer, inner) in [(a, b), (b, a)] {
                if !self.nodes[*inner.var()].is_and() {
                    continue;
                }
                let (x, y) = self.nodes[*inner.var()].fanin();
                if x == outer || y == outer {
                    if inner.polarity() {
                        return (inner, inner); // a & (a & b)
                    }
                    // a & !(a & b) = a & !b
                    reduced = Some((outer, !(if x == outer { y } else { x })));
                    break;
                }
                if x == !outer || y == !outer {
                    let result = if !inner.polarity() {
                        outer // a & !(!a & b)
                    } else {
                        Lit::constant(false) // a & (!a & b)
                    };
                    return (result, result);
                }
            }
            match reduced {
                Some(pair) => (a, b) = pair,
                None => return (a, b),
            }
        }
    }

    /// Drop everything outside the cone of influence of the roots (constraints,
    /// outputs, bads, justice, fairness and latches), then renumber the remaining
    /// nodes densely. Returns the refined AIG together with a map from original
    /// variables to refined variables, where unreachable variables map to `None`.
    pub fn coi_simplify(mut self) -> (Aig, VarMap<Var>) {
        let mut refine_map = VarMap::<Var>::new_with(Var(self.num_nodes() - 1));
        refine_map[Var::CONST] = Var::CONST;
        for edge in self
            .constraints
            .iter()
            .chain(self.outputs.iter())
            .chain(self.bads.iter())
            .chain(self.justice.iter().flatten())
            .chain(self.fairness.iter())
        {
            let var = edge.var();
            if refine_map[var].is_none() {
                refine_map[var] = Var::CONST;
            }
        }
        for latch in &self.latchs {
            for var in [
                Some(latch.input),
                Some(latch.next.var()),
                latch.init.map(|e| e.var()),
            ]
            .into_iter()
            .flatten()
            {
                if refine_map[var].is_none() {
                    refine_map[var] = Var::CONST;
                }
            }
        }
        for id in self.nodes_range_with_false().rev() {
            let var = Var::new(id as usize);
            if !refine_map[var].is_none() && self.nodes[*var].is_and() {
                let (fanin0, fanin1) = self.nodes[*var].fanin();
                for fanin in [fanin0.var(), fanin1.var()] {
                    refine_map[fanin] = Var::CONST;
                }
            }
        }
        let mut new_id = 0;
        for mapped in refine_map.iter_mut() {
            if !mapped.is_none() {
                let new = Var::new(new_id);
                new_id += 1;
                *mapped = new;
            }
        }
        let edge_map = |e: Lit| e.map_var(|v| refine_map[v]);
        let mut old_id = 0;
        self.nodes.retain_mut(|node| {
            let keep = !refine_map[Var::new(old_id)].is_none();
            old_id += 1;
            if keep && node.is_and() {
                node.fanin0 = edge_map(node.fanin0);
                node.fanin1 = edge_map(node.fanin1);
            }
            keep
        });
        self.inputs.retain_mut(|input| {
            let mapped = refine_map[*input];
            if mapped.is_none() {
                false
            } else {
                *input = mapped;
                true
            }
        });
        self.latchs.retain_mut(|latch| {
            let new_input = refine_map[latch.input];
            if !new_input.is_none() {
                latch.input = new_input;
                latch.next = edge_map(latch.next);
                if let Some(init) = &mut latch.init {
                    *init = edge_map(*init);
                }
                true
            } else {
                false
            }
        });
        for edge in self
            .outputs
            .iter_mut()
            .chain(self.bads.iter_mut())
            .chain(self.constraints.iter_mut())
            .chain(self.justice.iter_mut().flatten())
            .chain(self.fairness.iter_mut())
        {
            *edge = edge_map(*edge);
        }
        self.symbols = take(&mut self.symbols)
            .into_iter()
            .filter_map(|(old, symbol)| {
                let mapped = refine_map[old];
                (!mapped.is_none()).then_some((mapped, symbol))
            })
            .collect();
        (self, refine_map)
    }

    pub fn is_xor(&self, n: Var) -> Option<(Lit, Lit)> {
        if !self.nodes[*n].is_and() {
            return None;
        }
        let (fanin0, fanin1) = self.nodes[*n].fanin();
        if fanin0.polarity()
            || fanin1.polarity()
            || !self.nodes[*fanin0.var()].is_and()
            || !self.nodes[*fanin1.var()].is_and()
        {
            return None;
        }
        let (fanin00, fanin01) = self.nodes[*fanin0.var()].fanin();
        let (fanin10, fanin11) = self.nodes[*fanin1.var()].fanin();
        if fanin00 == !fanin10 && fanin01 == !fanin11 {
            return Some((fanin00, fanin01));
        }
        None
    }

    pub fn is_ite(&self, n: Var) -> Option<(Lit, Lit, Lit)> {
        if !self.nodes[*n].is_and() {
            return None;
        }
        let (fanin0, fanin1) = self.nodes[*n].fanin();
        if fanin0.polarity()
            || fanin1.polarity()
            || !self.nodes[*fanin0.var()].is_and()
            || !self.nodes[*fanin1.var()].is_and()
        {
            return None;
        }
        let (fanin00, fanin01) = self.nodes[*fanin0.var()].fanin();
        let (fanin10, fanin11) = self.nodes[*fanin1.var()].fanin();

        let (i, t, e) = if fanin00 == !fanin10 {
            (fanin00, !fanin01, !fanin11)
        } else if fanin00 == !fanin11 {
            (fanin00, !fanin01, !fanin10)
        } else if fanin01 == !fanin10 {
            (fanin01, !fanin00, !fanin11)
        } else if fanin01 == !fanin11 {
            (fanin01, !fanin00, !fanin10)
        } else {
            return None;
        };
        Some((i, t, e))
    }
}
