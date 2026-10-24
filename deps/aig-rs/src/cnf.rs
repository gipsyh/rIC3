use crate::Aig;
use giputils::gvec::Gvec;
use logicrs::{DagCnf, LitVvec, Var};

impl Aig {
    #[inline]
    fn get_root_refs(&self) -> Gvec<bool> {
        let mut refs = Gvec::from(vec![false; self.num_nodes() as _]);
        for l in self.latchs.iter() {
            refs[*l.next.var()] = true;
            if let Some(init) = &l.init {
                refs[*init.var()] = true;
            }
        }
        for l in self
            .constraints
            .iter()
            .chain(self.bads.iter())
            .chain(self.outputs.iter())
            .chain(self.justice.iter().flatten())
            .chain(self.fairness.iter())
        {
            refs[*l.var()] = true;
        }
        refs
    }

    pub fn cnf(&self, optimize: bool) -> DagCnf {
        let mut refs = self.get_root_refs();
        let mut ans = DagCnf::new();
        ans.new_var_to(Var(self.num_nodes() - 1));
        for i in self.nodes_range().rev() {
            if self.nodes[i].is_and() && refs[i] {
                let n = Var(i).lit();
                if optimize {
                    if let Some((xor0, xor1)) = self.is_xor(Var(i)) {
                        refs[*xor0.var()] = true;
                        refs[*xor1.var()] = true;
                        ans.add_rel_owned(n.var(), LitVvec::cnf_xor(n, xor0, xor1));
                        continue;
                    }
                    if let Some((c, t, e)) = self.is_ite(Var(i)) {
                        refs[*c.var()] = true;
                        refs[*t.var()] = true;
                        refs[*e.var()] = true;
                        ans.add_rel_owned(n.var(), LitVvec::cnf_ite(n, c, t, e));
                        continue;
                    }
                }
                let fanin0 = self.nodes[i].fanin0();
                let fanin1 = self.nodes[i].fanin1();
                refs[*fanin0.var()] = true;
                refs[*fanin1.var()] = true;
                ans.add_rel_owned(n.var(), LitVvec::cnf_and(n, &[fanin0, fanin1]));
            }
        }
        ans
    }

    /// Encode only the AIG nodes that survive gate recognition. The returned
    /// map translates original AIG variables to the dense CNF numbering; zero
    /// denotes an internal gate that was absorbed or is unreachable.
    pub fn cnf_compact(&self) -> (DagCnf, Gvec<Var>) {
        let mut refs = self.get_root_refs();
        // Count distinct parents in the recognized gate DAG, including an
        // extra use for external roots. Update these counts after each merge:
        // a shared descendant can become private as its parents are absorbed.
        let mut uses: Gvec<u32> = refs.iter().map(|&root| u32::from(root)).collect();
        for i in self.nodes_range().rev() {
            if !self.nodes[i].is_and() || !refs[i] {
                continue;
            }
            let mut mark = |v: Var| {
                refs[*v] = true;
                let index = usize::from(v);
                uses[index] += 1;
            };
            if let Some((x, y)) = self.is_xor(Var(i)) {
                mark(x.var());
                mark(y.var());
                continue;
            }
            if let Some((c, t, e)) = self.is_ite(Var(i)) {
                mark(c.var());
                mark(t.var());
                mark(e.var());
                continue;
            }
            let (a, b) = self.nodes[i].fanin();
            mark(a.var());
            if b.var() != a.var() {
                mark(b.var());
            }
        }

        let mut absorbed = Gvec::from(vec![false; self.num_nodes() as _]);
        let mut relations = Vec::new();
        for i in self.nodes_range().rev() {
            if !self.nodes[i].is_and() || !refs[i] || absorbed[i] {
                continue;
            }
            let n = Var(i);
            let mut rel = self.gate_cnf(n);
            let rel_lits = rel.num_lit();
            if uses[i] == 0 {
                for dep in relation_deps(&rel, n) {
                    uses[*dep] -= 1;
                }
                continue;
            }
            let dependencies = relation_deps(&rel, n);
            for &child in dependencies.iter().rev() {
                if uses[*child] != 1 || !self.nodes[*child].is_and() {
                    continue;
                }
                let definition = self.gate_cnf(child);
                let next = inline_gate(&rel, child, &definition);
                if next.num_lit() <= rel_lits + definition.num_lit() {
                    for &dep in &dependencies {
                        uses[*dep] -= 1;
                    }
                    for dep in relation_deps(&definition, child) {
                        uses[*dep] -= 1;
                    }
                    for dep in relation_deps(&next, n) {
                        uses[*dep] += 1;
                    }
                    rel = next;
                    absorbed[*child] = true;
                    break;
                }
            }
            relations.push((n, rel));
        }

        // Resolution can remove dependencies altogether (e.g. equal mux
        // branches). Recompute reachability before assigning dense numbers.
        refs = self.get_root_refs();
        for (n, rel) in &relations {
            if refs[**n] {
                for l in rel.iter().flatten() {
                    if l.var() != *n {
                        refs[*l.var()] = true;
                    }
                }
            }
        }
        let mut map = Gvec::from(vec![Var::CONST; self.num_nodes() as _]);
        let mut count = 0;
        for i in self.nodes_range() {
            if self.nodes[i].is_leaf() || (self.nodes[i].is_and() && refs[i] && !absorbed[i]) {
                count += 1;
                map[i] = Var::new(count);
            }
        }
        let mut ans = DagCnf::new();
        ans.new_var_to(Var::new(count));
        for (n, mut rel) in relations.into_iter().rev() {
            if !refs[*n] {
                continue;
            }
            for clause in rel.iter_mut() {
                for l in clause.iter_mut() {
                    *l = l.map_var(|v| {
                        let mapped = map[*v];
                        assert!(v.is_constant() || !mapped.is_constant());
                        mapped
                    });
                }
            }
            ans.add_rel_owned(map[*n], rel);
        }
        (ans, map)
    }

    fn gate_cnf(&self, n: Var) -> LitVvec {
        let mut rel = if let Some((x, y)) = self.is_xor(n) {
            LitVvec::cnf_xor(n.lit(), x, y)
        } else if let Some((c, t, e)) = self.is_ite(n) {
            LitVvec::cnf_ite(n.lit(), c, t, e)
        } else {
            let (a, b) = self.nodes[*n].fanin();
            LitVvec::cnf_and(n.lit(), &[a, b])
        };
        for clause in rel.iter_mut() {
            clause.sort_unstable();
        }
        rel
    }
}

fn relation_deps(rel: &LitVvec, output: Var) -> Vec<Var> {
    let mut deps: Vec<_> = rel
        .iter()
        .flatten()
        .map(|l| l.var())
        .filter(|&v| v != output)
        .collect();
    deps.sort_unstable();
    deps.dedup();
    deps
}

/// Eliminate a gate from the conjunction of parent and definition. Every
/// resolvent retains the parent's output, as required by DagCnf. The caller
/// must substitute all parents before removing the gate's own definition.
fn inline_gate(parent: &LitVvec, child: Var, definition: &LitVvec) -> LitVvec {
    let mut result = LitVvec::new();
    for clause in parent.iter() {
        let Some(pivot) = clause.iter().find(|l| l.var() == child) else {
            result.push(clause.clone());
            continue;
        };
        if clause.contains(&!(*pivot)) {
            continue; // A tautology must not become a constraint on resolution.
        }
        for other in definition.iter().filter(|c| c.contains(&!(*pivot))) {
            if let Some(resolvent) = clause.ordered_resolvent(other, child) {
                result.push(resolvent);
            }
        }
    }
    result.subsume_simplify();
    result
}
