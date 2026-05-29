use super::WlTransys;
use crate::wltransys::transform::{WlInnTermMapTf, WlRemoveTf, WlTransform, WlTransformStack};
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{FolOp, Term, TermType};
use std::{mem::take, ops::Deref};

impl WlTransys {
    pub fn coi_refine(&mut self) -> WlRemoveTf {
        CoiPass::apply(self).unwrap()
    }
    pub fn simplify(&mut self) -> WlTransformStack {
        let mut tf = WlTransformStack::new();
        if let Some(t) = ConstraintInputPass::apply(self) {
            tf.add(Box::new(t));
        }
        if let Some(t) = CoiPass::apply(self) {
            tf.add(Box::new(t));
        }
        if let Some(t) = InnTermSimpPass::apply(self) {
            tf.add(Box::new(t));
        }
        tf
    }
}

pub trait WlTsSimpPass {
    type WlTransform: WlTransform;

    fn apply(wts: &mut WlTransys) -> Option<Self::WlTransform>;
}

struct CoiPass;

impl WlTsSimpPass for CoiPass {
    type WlTransform = WlRemoveTf;

    fn apply(wts: &mut WlTransys) -> Option<Self::WlTransform> {
        let mut queue: Vec<_> = wts
            .constraint
            .iter()
            .chain(wts.bad.iter())
            .chain(wts.justice.iter())
            .cloned()
            .collect();
        for l in wts.latch.iter() {
            if let Some(init) = wts.init.get(l)
                && !init.is_const()
            {
                queue.push(init.clone());
                queue.push(l.clone());
            }
        }
        let mut touch: GHashSet<Term> = GHashSet::from_iter(queue.iter().cloned());
        while let Some(t) = queue.pop() {
            match &t.deref() {
                TermType::Const(_) => (),
                TermType::Var(_) => {
                    if let Some(n) = wts.next.get(&t)
                        && touch.insert(n.clone())
                    {
                        queue.push(n.clone());
                    }
                }
                TermType::Op(op) => {
                    for s in op.terms.iter() {
                        if touch.insert(s.clone()) {
                            queue.push(s.clone());
                        }
                    }
                }
            };
        }
        let mut removed = GHashSet::new();
        for x in take(&mut wts.input) {
            if touch.contains(&x) {
                wts.input.push(x);
            } else {
                removed.insert(x);
            }
        }
        for x in take(&mut wts.latch) {
            if touch.contains(&x) {
                wts.latch.push(x);
            } else {
                removed.insert(x);
            }
        }
        wts.init.retain(|k, _| touch.contains(k));
        wts.next.retain(|k, _| touch.contains(k));
        Some(WlRemoveTf::new(removed))
    }
}

struct InnTermSimpPass;

impl WlTsSimpPass for InnTermSimpPass {
    type WlTransform = WlInnTermMapTf;

    fn apply(wts: &mut WlTransys) -> Option<Self::WlTransform> {
        let mut map = GHashMap::new();
        for (_, i) in wts.init.iter_mut() {
            *i = i.simplify(&mut map);
        }
        for (_, n) in wts.next.iter_mut() {
            *n = n.simplify(&mut map);
        }
        for c in wts.constraint.iter_mut() {
            *c = c.simplify(&mut map);
        }
        wts.constraint
            .retain(|c| !c.try_bool_const().is_some_and(|f| f));
        for b in wts.bad.iter_mut() {
            *b = b.simplify(&mut map);
        }
        for j in wts.justice.iter_mut() {
            *j = j.simplify(&mut map);
        }
        Some(WlInnTermMapTf::new(map))
    }
}

pub struct ConstraintInputPass;

impl WlTsSimpPass for ConstraintInputPass {
    type WlTransform = WlTransformStack;

    fn apply(wts: &mut WlTransys) -> Option<WlTransformStack> {
        let inputs: GHashSet<_> = wts.input.iter().cloned().collect();
        let mut map = GHashMap::new();
        for cst in wts.constraint.iter() {
            if cst.is_var() && inputs.contains(cst) {
                map.insert(cst.clone(), true);
            } else if let Some(op) = cst.try_op() {
                if op.op == FolOp::Not && inputs.contains(&op.terms[0]) {
                    map.insert(cst.clone(), false);
                }
            }
        }
        dbg!(map.len());
        let tf = WlTransformStack::new();
        todo!()
    }
}
