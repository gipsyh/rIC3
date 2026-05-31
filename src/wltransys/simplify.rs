use super::WlTransys;
use crate::wltransys::transform::{
    WlExtTermMergeTf, WlInnTermMapTf, WlRemoveTf, WlTransform, WlTransformStack,
};
use giputils::hash::{GHashMap, GHashSet};
use log::debug;
use logicrs::{
    OptLevel,
    fol::{FolOp, Term, TermType, simplify::SimplifyCtx},
};
use std::{mem::take, ops::Deref};

impl WlTransys {
    pub fn term_apply(&mut self, r: impl Fn(&Term) -> Option<Term>) -> GHashMap<Term, Term> {
        let mut map = GHashMap::new();
        for input in self.input.iter_mut() {
            *input = input.cached_apply(&r, &mut map);
        }
        for latch in self.latch.iter_mut() {
            *latch = latch.cached_apply(&r, &mut map);
        }
        self.init = take(&mut self.init)
            .into_iter()
            .map(|(latch, init)| {
                (
                    latch.cached_apply(&r, &mut map),
                    init.cached_apply(&r, &mut map),
                )
            })
            .collect();
        self.next = take(&mut self.next)
            .into_iter()
            .map(|(latch, next)| {
                (
                    latch.cached_apply(&r, &mut map),
                    next.cached_apply(&r, &mut map),
                )
            })
            .collect();
        for bad in self.bad.iter_mut() {
            *bad = bad.cached_apply(&r, &mut map);
        }
        for constraint in self.constraint.iter_mut() {
            *constraint = constraint.cached_apply(&r, &mut map);
        }
        for justice in self.justice.iter_mut() {
            *justice = justice.cached_apply(&r, &mut map);
        }
        map
    }

    pub fn coi_refine(&mut self) -> WlRemoveTf {
        CoiPass::apply(&mut WlTsSimpCtx::default(), self, ()).unwrap()
    }

    pub fn simplify(&mut self, keep: &mut Vec<Term>) -> WlTransformStack {
        let mut ctx = WlTsSimpCtx { keep: keep.clone() };
        let mut tf = WlTransformStack::new();
        if let Some(t) = CoiPass::apply(&mut ctx, self, ()) {
            tf.add(t);
        }
        if let Some(t) = InnTermSimpPass::apply(&mut ctx, self, OptLevel::O0) {
            tf.add(t);
        }
        if let Some(t) = ConstraintInputPass::apply(&mut ctx, self, ()) {
            tf.add(t);
        }
        if let Some(t) = InnTermSimpPass::apply(&mut ctx, self, OptLevel::O3) {
            tf.add(t);
        }
        if let Some(t) = CoiPass::apply(&mut ctx, self, ()) {
            tf.add(t);
        }
        *keep = ctx.keep;
        tf
    }

    pub fn reset_to_init(&mut self, rst: &Term, polarity: bool) -> Option<WlTransformStack> {
        ResetToInitPass::apply(&mut WlTsSimpCtx::default(), self, (rst.clone(), polarity))
    }
}

pub trait WlTsSimpPass {
    type WlTransform: WlTransform;

    type PassArgs<'a>;

    fn apply<'a>(
        ctx: &mut WlTsSimpCtx,
        wts: &mut WlTransys,
        args: Self::PassArgs<'a>,
    ) -> Option<Self::WlTransform>;
}

#[derive(Default, Clone, Debug)]
pub struct WlTsSimpCtx {
    keep: Vec<Term>,
}

struct ResetToInitPass;

impl WlTsSimpPass for ResetToInitPass {
    type WlTransform = WlTransformStack;
    type PassArgs<'a> = (Term, bool);

    fn apply<'a>(
        _ctx: &mut WlTsSimpCtx,
        wts: &mut WlTransys,
        (rst, polarity): Self::PassArgs<'a>,
    ) -> Option<Self::WlTransform> {
        if !rst.is_var() || !rst.sort().is_bool() || !wts.input.iter().any(|i| i == &rst) {
            return None;
        }

        let reset_value = Term::bool_const(polarity);
        let normal_value = Term::bool_const(!polarity);
        let mut init_updates = Vec::new();
        let mut self_hold = 0;
        let mut non_const_init = 0;
        for latch in wts.latch.iter() {
            let Some(next) = wts.next.get(latch) else {
                continue;
            };
            let reset_next = next.apply(&|t| (t == &rst).then(|| reset_value.clone()));
            let normal_next = next.apply(&|t| (t == &rst).then(|| normal_value.clone()));
            if reset_next == normal_next {
                continue;
            }
            if reset_next == latch {
                self_hold += 1;
            } else if reset_next.is_const() {
                init_updates.push((latch.clone(), reset_next));
            } else {
                non_const_init += 1;
            }
        }
        if non_const_init > 0 {
            debug!("ResetToInitPass skipped because {non_const_init} reset values are non-const.");
            return None;
        }

        let const_init = init_updates.len();
        for (latch, reset_next) in init_updates {
            wts.init.insert(latch, reset_next);
        }

        let input: Vec<_> = take(&mut wts.input)
            .into_iter()
            .filter(|t| t != &rst)
            .collect();
        let ext_map = GHashMap::from_iter([(rst, normal_value)]);
        let mut inn_map = wts.term_apply(|t| ext_map.get(t).cloned());
        wts.input = input;
        for k in ext_map.keys() {
            inn_map.remove(k);
        }

        debug!(
            "ResetToInitPass moved {const_init} const reset values to init and kept {self_hold} self-holding reset values unconstrained."
        );
        let mut tf = WlTransformStack::new();
        tf.add(WlInnTermMapTf::new(inn_map));
        tf.add(WlExtTermMergeTf::new(ext_map));
        Some(tf)
    }
}

struct CoiPass;

impl WlTsSimpPass for CoiPass {
    type WlTransform = WlRemoveTf;
    type PassArgs<'a> = ();

    fn apply<'a>(
        ctx: &mut WlTsSimpCtx,
        wts: &mut WlTransys,
        _args: Self::PassArgs<'a>,
    ) -> Option<Self::WlTransform> {
        let mut queue: Vec<_> = wts
            .constraint
            .iter()
            .chain(wts.bad.iter())
            .chain(wts.justice.iter())
            .chain(ctx.keep.iter())
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
    type PassArgs<'a> = OptLevel;

    fn apply<'a>(
        ctx: &mut WlTsSimpCtx,
        wts: &mut WlTransys,
        opt: Self::PassArgs<'a>,
    ) -> Option<Self::WlTransform> {
        let mut map = GHashMap::new();
        let fol_ctx = SimplifyCtx::new(opt);
        for (_, i) in wts.init.iter_mut() {
            *i = i.simplify_with_ctx(&fol_ctx, &mut map);
        }
        for (_, n) in wts.next.iter_mut() {
            *n = n.simplify_with_ctx(&fol_ctx, &mut map);
        }
        for c in wts.constraint.iter_mut() {
            *c = c.simplify_with_ctx(&fol_ctx, &mut map);
        }
        wts.constraint
            .retain(|c| !c.try_bool_const().is_some_and(|f| f));
        for b in wts.bad.iter_mut() {
            *b = b.simplify_with_ctx(&fol_ctx, &mut map);
        }
        for j in wts.justice.iter_mut() {
            *j = j.simplify_with_ctx(&fol_ctx, &mut map);
        }
        for t in ctx.keep.iter_mut() {
            *t = t.simplify_with_ctx(&fol_ctx, &mut map);
        }
        Some(WlInnTermMapTf::new(map))
    }
}

pub struct ConstraintInputPass;

impl WlTsSimpPass for ConstraintInputPass {
    type WlTransform = WlTransformStack;
    type PassArgs<'a> = ();

    fn apply<'a>(
        ctx: &mut WlTsSimpCtx,
        wts: &mut WlTransys,
        _args: Self::PassArgs<'a>,
    ) -> Option<WlTransformStack> {
        let inputs: GHashSet<_> = wts.input.iter().cloned().collect();
        let keep: GHashSet<_> = ctx.keep.iter().cloned().collect();
        let mut ext_map = GHashMap::new();
        for cst in wts.constraint.iter() {
            if cst.is_var() && inputs.contains(cst) {
                if !keep.contains(cst) {
                    ext_map.insert(cst.clone(), Term::bool_const(true));
                }
            } else if let Some(op) = cst.try_op() {
                if op.op == FolOp::Not && inputs.contains(&op.terms[0]) {
                    let input = &op.terms[0];
                    if !keep.contains(input) {
                        ext_map.insert(input.clone(), Term::bool_const(false));
                    }
                }
            }
        }
        if ext_map.is_empty() {
            return None;
        }
        let input: Vec<_> = take(&mut wts.input)
            .into_iter()
            .filter(|t| !ext_map.contains_key(t))
            .collect();
        let mut inn_map = wts.term_apply(|t| ext_map.get(t).cloned());
        wts.input = input;
        for k in ext_map.keys() {
            inn_map.remove(k);
        }
        debug!("ConstraintInputPass removed {} inputs.", ext_map.len());
        let inn_map = WlInnTermMapTf::new(inn_map);
        let ext_map = WlExtTermMergeTf::new(ext_map);
        let mut tf = WlTransformStack::new();
        tf.add(inn_map);
        tf.add(ext_map);
        Some(tf)
    }
}
