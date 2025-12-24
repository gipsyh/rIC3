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
        let mut latchs = LitVec::new();
        for latch in self.ts.latch() {
            let lit = latch.lit();
            if self.slv.domain_has(lit.var())
                && let Some(v) = satif.sat_value(lit)
                && (in_cls.contains(&latch) || !satif.flip_to_none(latch))
            {
                latchs.push(lit.not_if(!v));
            }
        }
        for i in 0.. {
            if latchs.is_empty() {
                break;
            }
            if !order(i, &mut latchs) {
                break;
            }
            let olen = latchs.len();
            latchs = self
                .slv
                .minimal_premise(&inputs_flatten, &latchs, &cls)
                .unwrap();
            if latchs.len() == olen {
                break;
            }
        }
        self.slv.unset_domain();
        (latchs, inputs)
    }
}
