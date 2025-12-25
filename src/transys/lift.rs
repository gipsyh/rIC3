use crate::{
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf, unroll::TransysUnroll},
};
use giputils::hash::GHashSet;
use logicrs::{Lit, LitVec, Var, satif::Satif};

pub struct TsLift {
    ts: TransysUnroll<Transys>,
    slv: DagCnfSolver,
}

impl TsLift {
    pub fn new(ts: TransysUnroll<Transys>) -> Self {
        let tsc = ts.compile();
        let slv = DagCnfSolver::new(&tsc.rel);
        Self { ts, slv }
    }

    pub fn lift(
        &mut self,
        satif: &mut impl Satif,
        target: impl IntoIterator<Item = impl AsRef<Lit>>,
        order: impl FnMut(usize, &mut [Lit]) -> bool,
    ) -> (LitVec, Vec<LitVec>) {
        self.complex_lift(satif, self.ts.latch.clone(), target, order)
    }

    pub fn complex_lift(
        &mut self,
        satif: &mut impl Satif,
        state: impl IntoIterator<Item = impl AsRef<Var>>,
        target: impl IntoIterator<Item = impl AsRef<Lit>>,
        mut order: impl FnMut(usize, &mut [Lit]) -> bool,
    ) -> (LitVec, Vec<LitVec>) {
        let mut cls: LitVec = target.into_iter().map(|l| *l.as_ref()).collect();
        if cls.is_empty() {
            return (LitVec::new(), vec![]);
        }
        cls = !cls;
        let in_cls: GHashSet<Var> = GHashSet::from_iter(cls.iter().map(|l| l.var()));
        let mut inputs = Vec::new();
        let mut inputs_flatten = LitVec::new();
        for k in 0..=self.ts.num_unroll {
            let mut input = LitVec::new();
            for i in self.ts.input() {
                let lit = self.ts.lit_next(i.lit(), k);
                if let Some(v) = satif.sat_value(lit) {
                    input.push(i.lit().not_if(!v));
                    inputs_flatten.push(lit.not_if(!v));
                }
            }
            inputs.push(input);
        }
        self.slv.set_domain(cls.iter().cloned());
        let mut states = LitVec::new();
        for s in state.into_iter() {
            let s = *s.as_ref();
            let lit = s.lit();
            if self.slv.domain_has(lit.var())
                && let Some(v) = satif.sat_value(lit)
                && (in_cls.contains(&s) || !satif.flip_to_none(s))
            {
                states.push(lit.not_if(!v));
            }
        }
        for i in 0.. {
            if states.is_empty() {
                break;
            }
            if !order(i, &mut states) {
                break;
            }
            let olen = states.len();
            states = self
                .slv
                .minimal_premise(&inputs_flatten, &states, &cls)
                .unwrap();
            if states.len() == olen {
                break;
            }
        }
        self.slv.unset_domain();
        (states, inputs)
    }
}
