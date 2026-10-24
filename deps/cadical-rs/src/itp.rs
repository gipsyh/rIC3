use crate::tracer::Tracer;
use aig::Aig;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::{Lit, LitVec, Var};
use std::mem::take;

#[derive(Default)]
pub struct Interpolant {
    b_vars: GHashSet<Var>,
    var_edge: GHashMap<Var, Var>,
    cls_labels: GHashMap<usize, bool>,
    next_cls_label: Option<bool>,
    aig: Aig,
    itp: GHashMap<usize, Lit>,
    clauses: GHashMap<usize, LitVec>,
    mark: GHashSet<Lit>,
    handle_a: bool,
}

impl Interpolant {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn label_clause(&mut self, k: bool) {
        self.next_cls_label = Some(k)
    }

    pub fn interpolant(self) -> (Aig, GHashMap<Var, Var>) {
        (self.aig, self.var_edge)
    }
}

impl Tracer for Interpolant {
    fn add_original_clause(&mut self, id: usize, _redundant: bool, c: &[Lit], restore: bool) {
        // println!("o {id}, {:?}", c);
        if !restore {
            assert!(
                self.cls_labels
                    .insert(id, take(&mut self.next_cls_label).unwrap())
                    .is_none()
            );
        }
        let itp = if self.cls_labels[&id] {
            assert!(!self.handle_a);
            for l in c.iter() {
                self.b_vars.insert(l.var());
            }
            Lit::constant(true)
        } else {
            self.handle_a = true;
            let mut itp = Lit::constant(false);
            for l in c.iter().filter(|l| self.b_vars.contains(&l.var())) {
                let e = if let Some(e) = self.var_edge.get(&l.var()) {
                    *e
                } else {
                    let e = self.aig.new_input();
                    self.var_edge.insert(l.var(), e);
                    e
                };
                let e = Lit::new(e, l.polarity());
                itp = self.aig.new_or_node(itp, e);
            }
            itp
        };
        self.itp.insert(id, itp);
        self.clauses.insert(id, LitVec::from(c));
    }

    fn add_derived_clause(&mut self, id: usize, _redundant: bool, c: &[Lit], p: &[usize]) {
        // println!("d {id}, {:?}, {:?}", c, p);
        let conflict = p.last().unwrap();
        for l in self.clauses[conflict].iter() {
            self.mark.insert(*l);
        }
        let mut itp = self.itp[conflict];
        for pi in (0..p.len() - 1).rev() {
            for l in self.clauses[&p[pi]].iter() {
                if self.mark.contains(&!*l) {
                    itp = if self.b_vars.contains(&l.var()) {
                        self.aig.new_and_node(itp, self.itp[&p[pi]])
                    } else {
                        self.aig.new_or_node(itp, self.itp[&p[pi]])
                    };
                }
                self.mark.insert(*l);
            }
        }
        self.mark.clear();
        self.itp.insert(id, itp);
        self.clauses.insert(id, LitVec::from(c));
    }

    fn delete_clause(&mut self, id: usize, _redundant: bool, _c: &[Lit]) {
        self.itp.remove(&id);
        self.clauses.remove(&id);
    }

    fn conclude_unsat(&mut self, conclusion: i32, p: &[usize]) {
        if conclusion == 1 {
            assert!(p.len() == 1);
            self.aig.outputs.push(self.itp[&p[0]]);
            let (aig, map) = take(&mut self.aig).coi_simplify();
            self.aig = aig;
            let ve = take(&mut self.var_edge);
            for (v, e) in ve {
                let mapped = map[e];
                if !mapped.is_none() {
                    self.var_edge.insert(v, mapped);
                }
            }
        } else {
            todo!();
        }
    }
}
