use super::abc::abc_preprocess;
use crate::options;
use aig::Aig;
use giputils::hash::{GHashMap, GHashSet};
use logic_form::Var;

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
