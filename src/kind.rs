use crate::{
    BlProof, Engine, McProof, McResult, McWitness,
    config::{EngineConfigBase, PreprocConfig},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    transys::{Transys, TransysIf, certify::Restore, nodep::NoDepTransys, unroll::TransysUnroll},
};
use clap::Args;
use log::{error, info};
use logicrs::{Lit, LitVec, Var, satif::Satif};
use serde::{Deserialize, Serialize};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct KindConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,

    /// simple path constraint
    #[arg(long = "simple-path", default_value_t = false)]
    pub simple_path: bool,
}

impl_config_deref!(KindConfig);

pub struct Kind {
    uts: TransysUnroll<NoDepTransys>,
    cfg: KindConfig,
    solver: Box<dyn Satif>,
    slv_trans_k: usize,
    slv_bad_k: usize,
    ots: Transys,
    rst: Restore,
    tracer: Tracer,
}

impl Kind {
    pub fn new(cfg: KindConfig, mut ts: Transys) -> Self {
        let ots = ts.clone();
        ts.compress_bads();
        let rst = Restore::new(&ts);
        let (mut ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        ts.remove_gate_init(&mut rst);
        let mut ts = ts.remove_dep();
        ts.assert_constraint();
        if cfg.preproc.preproc {
            ts.simplify(&mut rst);
        }
        let mut uts = TransysUnroll::new(&ts);
        if cfg.simple_path {
            uts.enable_simple_path();
        }
        let solver: Box<dyn Satif> = Box::new(cadical::CaDiCaL::new());
        Self {
            uts,
            cfg,
            solver,
            slv_trans_k: 0,
            slv_bad_k: 0,
            ots,
            rst,
            tracer: Tracer::new(),
        }
    }

    pub fn load_trans_to(&mut self, k: usize) {
        self.slv_trans_k = self.uts.load_trans_to(self.solver.as_mut(), self.slv_trans_k, k);
    }

    pub fn load_bad_to(&mut self, k: usize) {
        while self.slv_bad_k < k + 1 {
            let bad: LitVec = self
                .uts
                .lits_next(&self.uts.ts.bad, self.slv_bad_k)
                .collect();
            self.solver.add_clause(&!bad);
            self.slv_bad_k += 1;
        }
    }
}

impl Engine for Kind {
    fn check(&mut self) -> McResult {
        let step = self.cfg.step as usize;
        if step != 1 {
            error!("k-induction step should be 1, got {step}");
            panic!();
        }
        if self.cfg.start != 0 {
            error!("k-induction start should be 0, got {}", self.cfg.start);
            panic!();
        }
        for k in 0..=self.cfg.end {
            self.uts.unroll_to(k);
            self.load_trans_to(k);
            if k > 0 {
                self.load_bad_to(k - 1);
                let assump: LitVec = self.uts.lits_next(&self.uts.ts.bad, k).collect();
                let res = self.solver.solve(&assump);
                if !res {
                    self.tracer.trace_res(McResult::Safe);
                    return McResult::Safe;
                }
            }
            let mut assump: LitVec = self.uts.ts.inits().iter().flatten().copied().collect();
            assump.extend(self.uts.lits_next(&self.uts.ts.bad, k));
            if self.solver.solve(&assump) {
                self.tracer.trace_res(McResult::Unsafe(k));
                return McResult::Unsafe(k);
            }
            self.tracer.trace_res(McResult::Unknown(Some(k)));
        }
        info!("kind reached bound {}, stopping search", self.cfg.end);
        McResult::Unknown(Some(self.cfg.end))
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn proof(&mut self) -> McProof {
        if self.cfg.simple_path {
            //TODO: support certifaiger with simple path constraint
            error!("k-induction with simple path constraint not support certifaiger");
            panic!();
        }
        let mut ts = self.ots.clone();
        let eqi = self.rst.eq_invariant();
        let mut certifaiger_dnf = vec![];
        for cube in eqi {
            certifaiger_dnf.push(ts.rel.new_and(cube));
        }
        certifaiger_dnf.extend(ts.bad);
        let invariants = ts.rel.new_or(certifaiger_dnf);
        ts.bad = LitVec::from(invariants);
        if !ts.constraint.is_empty() {
            ts.constraint = LitVec::from([ts.rel.new_and(ts.constraint)]);
        }
        let mut proof = ts.clone();
        let ni = proof.input.len();
        let nl = proof.latch.len();
        let k = self.uts.num_unroll;
        let mut inputs = proof.input.clone();
        let mut latchs = proof.latch.clone();
        let mut next = proof.next.clone();
        let mut inits = proof.init.clone();
        let mut bads = proof.bad.clone();
        let mut constrains = proof.constraint.clone();
        for _ in 1..k {
            let offset = proof.max_var();
            let map = |x: Var| {
                if x == Var::CONST { x } else { x + offset }
            };
            proof.new_var_to(map(ts.max_var()));
            let lmap = |x: Lit| Lit::new(map(x.var()), x.polarity());
            for v in Var(1)..=ts.max_var() {
                let rel: Vec<LitVec> = ts.rel[v].iter().map(|cls| cls.map(lmap)).collect();
                let mv = map(v);
                proof.rel.add_rel(mv, &rel);
            }
            for &i in ts.input.iter() {
                inputs.push(map(i));
            }
            for &l in ts.latch.iter() {
                let ml = map(l);
                latchs.push(ml);
                next.insert(ml, lmap(ts.next[&l]));
                if let Some(i) = ts.init.get(&l) {
                    inits.insert(ml, lmap(*i));
                }
            }
            bads.extend(ts.bad.map(lmap));
            for &l in ts.constraint.iter() {
                constrains.push(lmap(l));
            }
        }
        if !constrains.is_empty() {
            for i in 0..k {
                bads[i] = proof.rel.new_or([bads[i], !constrains[i]]);
            }
        }
        let sum = inputs.len() + latchs.len();
        let mut aux_latchs: Vec<Lit> = Vec::new();
        for i in 0..k {
            let aux = proof.new_var().lit();
            aux_latchs.push(aux);
            let (next, init) = if i == 0 {
                (aux, Some(Lit::constant(true)))
            } else {
                (aux_latchs[i - 1], Some(Lit::constant(false)))
            };
            proof.add_latch(aux.var(), init, next);
        }
        for i in 1..k {
            for j in 0..ni {
                proof.add_latch(inputs[j + i * ni], None, inputs[j + (i - 1) * ni].lit());
            }
            for j in 0..nl {
                proof.add_latch(latchs[j + i * nl], None, latchs[j + (i - 1) * nl].lit());
            }
        }
        for i in 0..k {
            let al = aux_latchs[i];
            let p = proof.rel.new_imply(al, !bads[i]);
            bads[i] = !p;
        }

        for i in 1..k {
            let al = aux_latchs[i];
            let al_next = aux_latchs[i - 1];
            let p = proof.rel.new_imply(al, al_next);
            bads.push(!p);
            let mut eqs = Vec::new();
            let mut init = Vec::new();
            for j in 0..nl {
                let lis1j = latchs[(i - 1) * nl + j];
                if let Some(&linit) = inits.get(&lis1j) {
                    init.push(LitVec::from([lis1j.lit(), !linit]));
                    init.push(LitVec::from([!lis1j.lit(), linit]));
                }
                eqs.push(
                    proof
                        .rel
                        .new_xnor(next[&latchs[j + i * nl]], latchs[j + (i - 1) * nl].lit()),
                );
            }
            let p = proof.rel.new_and(eqs);
            let p = proof.rel.new_imply(al, p);
            bads.push(!p);
            let init: Vec<_> = init.into_iter().map(|cls| proof.rel.new_or(cls)).collect();
            let init = proof.rel.new_and(init);
            let p = proof.rel.new_and([!al, al_next]);
            let p = proof.rel.new_imply(p, init);
            bads.push(!p);
        }
        bads.push(!aux_latchs[0]);
        proof.bad = LitVec::from(proof.rel.new_or(bads));
        assert!(proof.input.len() + proof.latch.len() == sum + k);
        McProof::Bl(BlProof { proof })
    }

    fn witness(&mut self) -> McWitness {
        let mut wit = self.uts.witness(self.solver.as_ref());
        let iv = self.rst.init_var();
        wit = wit.filter_map(|l| (iv != Some(l.var())).then(|| self.rst.restore(l)));
        for s in wit.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        wit.exact_state(&self.ots);
        McWitness::Bl(wit)
    }
}
