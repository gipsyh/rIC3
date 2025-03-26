use super::abc::abc_preprocess;
use crate::{options, transys::Transys};
use aig::Aig;
use giputils::hash::{GHashMap, GHashSet};
use logic_form::{LitVec, Var};

pub fn aig_preprocess(aig: &Aig, options: &options::Options) -> (Aig, GHashMap<Var, Var>) {
    let (mut aig, mut remap) = aig.coi_refine();
    if !(options.preprocess.no_abc
        || matches!(options.engine, options::Engine::IC3) && options.ic3.inn)
    {
        let mut remap_retain = GHashSet::new();
        remap_retain.insert(Var::CONST);
        for i in aig.inputs.iter() {
            remap_retain.insert((*i).into());
        }
        for l in aig.latchs.iter() {
            remap_retain.insert(l.input.into());
        }
        remap.retain(|x, _| remap_retain.contains(x));
        aig = abc_preprocess(aig);
        let remap2;
        (aig, remap2) = aig.coi_refine();
        remap = {
            let mut remap_final = GHashMap::new();
            for (x, y) in remap2 {
                if let Some(z) = remap.get(&y) {
                    remap_final.insert(x, *z);
                }
            }
            remap_final
        }
    }
    aig.constraints.retain(|e| !e.is_constant(true));
    (aig, remap)
}

pub fn aig2ts(aig: &Aig, rst: &GHashMap<Var, Var>) -> Transys {
    let input: Vec<Var> = aig.inputs.iter().map(|x| Var::new(*x)).collect();
    let constraint: LitVec = aig.constraints.iter().map(|c| c.to_lit()).collect();
    let mut latch = Vec::new();
    let mut next = GHashMap::new();
    let mut init = GHashMap::new();
    for l in aig.latchs.iter() {
        let lv = Var::from(l.input);
        latch.push(lv);
        next.insert(lv, l.next.to_lit());
        if let Some(i) = l.init {
            init.insert(lv, i);
        }
    }
    let bad = aig.bads[0].to_lit();
    let rel = aig.get_cnf();
    Self {
        input,
        latch,
        next,
        init,
        bad,
        constraint,
        rel,
        rst: rst.clone(),
    }
}