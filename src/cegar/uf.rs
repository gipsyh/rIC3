use super::CegarAbstractor;
use crate::wltransys::WlTransys;
use crate::{WlCex, WlProof};
use giputils::hash::GHashMap;
use log::info;
use logicrs::fol::{
    Sort, Term, TermType,
    op::{self, DynOp},
};
use std::{mem::take, ops::Deref};

pub struct UfAbstraction {
    pub wts: WlTransys,
    pub output_subst: GHashMap<Term, Term>,
    pub stats: UfStats,
}

#[derive(Clone, Debug, Default)]
pub struct UfStats {
    pub applications: usize,
    pub outputs: usize,
    pub constraints: usize,
}

#[derive(Clone)]
struct UfApp {
    op: DynOp,
    args: Vec<Term>,
    result: Term,
    history: Option<UfHistory>,
}

#[derive(Clone)]
struct UfHistory {
    valid: Term,
    args: Vec<Term>,
    result: Term,
}

pub struct UfAbstractor {
    cache: GHashMap<Term, Term>,
    outputs: GHashMap<(DynOp, Sort, Vec<Term>), Term>,
    output_subst: GHashMap<Term, Term>,
    apps: Vec<UfApp>,
    stats: UfStats,
}

pub struct Uf {
    origin: WlTransys,
    output_subst: GHashMap<Term, Term>,
    stats: UfStats,
}

impl Uf {
    pub fn new(origin: WlTransys) -> Self {
        Self {
            origin,
            output_subst: GHashMap::new(),
            stats: UfStats::default(),
        }
    }

    fn substitute_outputs(&self, mut proof: WlProof) -> WlProof {
        proof
            .input
            .retain(|input| !self.output_subst.contains_key(input));

        let mut cache = GHashMap::new();
        for init in proof.init.values_mut() {
            *init = self.substitute_term(init, &mut cache);
        }
        for next in proof.next.values_mut() {
            *next = self.substitute_term(next, &mut cache);
        }
        for bad in proof.bad.iter_mut() {
            *bad = self.substitute_term(bad, &mut cache);
        }
        for constraint in proof.constraint.iter_mut() {
            *constraint = self.substitute_term(constraint, &mut cache);
        }
        for justice in proof.justice.iter_mut() {
            *justice = self.substitute_term(justice, &mut cache);
        }
        proof
    }

    fn substitute_term(&self, term: &Term, cache: &mut GHashMap<Term, Term>) -> Term {
        term.cached_apply(&|term| self.output_subst.get(term).cloned(), cache)
    }
}

impl CegarAbstractor for Uf {
    fn name(&self) -> &'static str {
        "uf"
    }

    fn abstract_wts(&mut self) -> WlTransys {
        let mut abstractor = UfAbstractor::new();
        let result = abstractor.abstract_transys(self.origin.clone());
        info!(
            "cegar uf abstracted {} applications into {} fresh inputs and {} consistency constraints",
            result.stats.applications, result.stats.outputs, result.stats.constraints,
        );
        self.output_subst = result.output_subst;
        self.stats = result.stats;
        result.wts
    }

    fn refine(&mut self, _cex: &WlCex) -> Option<WlTransys> {
        None
    }

    fn proof(&self, proof: WlProof) -> WlProof {
        self.substitute_outputs(proof)
    }
}

impl UfAbstractor {
    pub fn new() -> Self {
        Self {
            cache: GHashMap::new(),
            outputs: GHashMap::new(),
            output_subst: GHashMap::new(),
            apps: Vec::new(),
            stats: UfStats::default(),
        }
    }

    pub fn abstract_transys(&mut self, mut wts: WlTransys) -> UfAbstraction {
        for init in wts.init.values_mut() {
            *init = self.abstract_term(init);
        }
        for next in wts.next.values_mut() {
            *next = self.abstract_term(next);
        }
        for bad in wts.bad.iter_mut() {
            *bad = self.abstract_term(bad);
        }
        for constraint in wts.constraint.iter_mut() {
            *constraint = self.abstract_term(constraint);
        }
        for justice in wts.justice.iter_mut() {
            *justice = self.abstract_term(justice);
        }

        wts.input
            .extend(self.apps.iter().map(|app| app.result.clone()));
        self.add_history(&mut wts);
        wts.constraint.extend(self.consistency_constraints());

        self.stats.applications = self.apps.len();
        self.stats.outputs = self.outputs.len();

        UfAbstraction {
            wts,
            output_subst: take(&mut self.output_subst),
            stats: self.stats.clone(),
        }
    }

    fn abstract_term(&mut self, term: &Term) -> Term {
        if let Some(term) = self.cache.get(term) {
            return term.clone();
        }

        let abstracted = match term.deref() {
            TermType::Op(op_term) => {
                let args: Vec<Term> = op_term
                    .terms
                    .iter()
                    .map(|term| self.abstract_term(term))
                    .collect();
                if should_abstract(&op_term.op) {
                    self.uf_output(&op_term.op, term, args)
                } else {
                    Term::new_op(op_term.op.clone(), args)
                }
            }
            _ => term.clone(),
        };

        self.cache.insert(term.clone(), abstracted.clone());
        abstracted
    }

    fn uf_output(&mut self, op: &DynOp, concrete: &Term, args: Vec<Term>) -> Term {
        let sort = concrete.sort();
        let key = (op.clone(), sort, args.clone());
        if let Some(output) = self.outputs.get(&key) {
            return output.clone();
        }

        let output = Term::new_var(sort);
        self.outputs.insert(key, output.clone());
        self.output_subst.insert(output.clone(), concrete.clone());
        self.apps.push(UfApp {
            op: op.clone(),
            args,
            result: output.clone(),
            history: None,
        });
        output
    }

    fn add_history(&mut self, wts: &mut WlTransys) {
        for app in self.apps.iter_mut() {
            let valid = Term::new_var(Sort::bool());
            wts.add_latch(
                valid.clone(),
                Some(Term::bool_const(false)),
                Term::bool_const(true),
            );

            let args: Vec<Term> = app
                .args
                .iter()
                .map(|arg| {
                    let history = Term::new_var(arg.sort());
                    wts.add_latch(history.clone(), None, arg.clone());
                    history
                })
                .collect();

            let result = Term::new_var(app.result.sort());
            wts.add_latch(result.clone(), None, app.result.clone());

            app.history = Some(UfHistory {
                valid,
                args,
                result,
            });
        }
    }

    fn consistency_constraints(&mut self) -> Vec<Term> {
        let mut constraints = Vec::new();
        let apps = take(&mut self.apps);

        for i in 0..apps.len() {
            for j in (i + 1)..apps.len() {
                if !same_signature(&apps[i], &apps[j]) {
                    continue;
                }
                constraints.push(
                    same_args(&apps[i].args, &apps[j].args)
                        .imply(apps[i].result.teq(&apps[j].result)),
                );
            }
        }

        for current in apps.iter() {
            for previous in apps.iter() {
                if !same_history_signature(current, previous) {
                    continue;
                }
                let previous = previous.history.as_ref().unwrap();
                constraints.push(
                    previous.valid.imply(
                        same_args(&current.args, &previous.args)
                            .imply(current.result.teq(&previous.result)),
                    ),
                );
            }
        }

        self.stats.constraints = constraints.len();
        self.apps = apps;
        constraints
    }
}

fn should_abstract(op: &DynOp) -> bool {
    op == &op::Mul
        || op == &op::Udiv
        || op == &op::Urem
        || op == &op::Sdiv
        || op == &op::Srem
        || op == &op::Smod
}

fn same_signature(lhs: &UfApp, rhs: &UfApp) -> bool {
    lhs.op == rhs.op
        && lhs.result.sort() == rhs.result.sort()
        && same_arg_sorts(&lhs.args, &rhs.args)
}

fn same_history_signature(current: &UfApp, previous: &UfApp) -> bool {
    let Some(history) = previous.history.as_ref() else {
        return false;
    };
    current.op == previous.op
        && current.result.sort() == history.result.sort()
        && same_arg_sorts(&current.args, &history.args)
}

fn same_arg_sorts(lhs: &[Term], rhs: &[Term]) -> bool {
    lhs.len() == rhs.len()
        && lhs
            .iter()
            .zip(rhs.iter())
            .all(|(lhs, rhs)| lhs.sort() == rhs.sort())
}

fn same_args(lhs: &[Term], rhs: &[Term]) -> Term {
    debug_assert!(same_arg_sorts(lhs, rhs));
    Term::new_ands(lhs.iter().zip(rhs.iter()).map(|(lhs, rhs)| lhs.teq(rhs)))
}
