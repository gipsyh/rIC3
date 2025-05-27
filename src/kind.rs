use crate::{
    Engine, Proof, Witness,
    config::Config,
    transys::{Transys, TransysIf, nodep::NoDepTransys, unroll::TransysUnroll},
};
use log::{error, info};
use logic_form::{Lit, LitVec, Var};
use satif::Satif;

pub struct Kind {
    uts: TransysUnroll<NoDepTransys>,
    cfg: Config,
    solver: Box<dyn Satif>,
}

impl Kind {
    pub fn new(cfg: Config, ts: Transys) -> Self {
        let mut ts = ts.remove_dep();
        ts.assert_constraint();
        ts.simplify();
        let uts = if cfg.kind.simple_path {
            TransysUnroll::new_with_simple_path(&ts)
        } else {
            TransysUnroll::new(&ts)
        };
        let solver: Box<dyn Satif> = if cfg.kind.kind_kissat {
            Box::new(kissat::Solver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
        Self { uts, cfg, solver }
    }

    pub fn reset_solver(&mut self) {
        self.solver = if self.cfg.kind.kind_kissat {
            Box::new(kissat::Solver::new())
        } else {
            Box::new(cadical::Solver::new())
        };
    }
}

impl Engine for Kind {
    fn check(&mut self) -> Option<bool> {
        let step = self.cfg.step as usize;
        self.uts.load_trans(self.solver.as_mut(), 0, true);
        for k in (step..).step_by(step) {
            let bmc_k = k - 1;
            let start = k + 1 - step;
            if self.cfg.kind.kind_kissat {
                self.reset_solver();
                for i in 0..start {
                    self.uts.load_trans(self.solver.as_mut(), i, true);
                }
                if bmc_k >= step {
                    for i in 0..=bmc_k - step {
                        self.solver
                            .add_clause(&!self.uts.lits_next(&self.uts.ts.bad.cube(), i));
                    }
                }
            }
            self.uts.unroll_to(bmc_k);
            for i in start..=bmc_k {
                self.uts.load_trans(self.solver.as_mut(), i, true);
            }
            if !self.cfg.kind.no_bmc {
                let mut assump: LitVec = self.uts.ts.init().collect();
                assump.extend_from_slice(&self.uts.lits_next(&self.uts.ts.bad.cube(), bmc_k));
                info!("kind bmc depth: {bmc_k}");
                if self.solver.solve(&assump) {
                    info!("bmc found counter-example in depth {bmc_k}");
                    return Some(false);
                }
            }
            for i in bmc_k + 1 - step..=bmc_k {
                self.solver
                    .add_clause(&!self.uts.lits_next(&self.uts.ts.bad.cube(), i));
            }
            self.uts.unroll_to(k);
            self.uts.load_trans(self.solver.as_mut(), k, true);
            info!("kind depth: {k}");
            let res = if self.cfg.kind.kind_kissat {
                for l in self.uts.lits_next(&self.uts.ts.bad.cube(), k) {
                    self.solver.add_clause(&[l]);
                }
                self.solver.solve(&[])
            } else {
                self.solver
                    .solve(&self.uts.lits_next(&self.uts.ts.bad.cube(), k))
            };
            if !res {
                info!("k-induction proofed in depth {k}");
                return Some(true);
            }
        }
        unreachable!();
    }

    fn proof(&mut self, ts: &Transys) -> Proof {
        if self.cfg.kind.simple_path {
            //TODO: support certifaiger with simple path constraint
            error!("k-induction with simple path constraint not support certifaiger");
            panic!();
        }
        let mut ts = ts.clone();
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
        let mut bads = vec![proof.bad];
        let mut constrains = proof.constraint.clone();
        for _ in 1..k {
            let offset = proof.max_var();
            let map = |x: Var| {
                if x == Var::CONST { x } else { x + offset }
            };
            proof.new_var_to(map(ts.max_var()));
            let lmap = |x: Lit| Lit::new(map(x.var()), x.polarity());
            for v in Var(1)..=ts.max_var() {
                let rel: Vec<LitVec> = ts.rel[v]
                    .iter()
                    .map(|cls| cls.iter().map(|l| lmap(*l)).collect())
                    .collect();
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
                    inits.insert(ml, *i);
                }
            }
            bads.push(lmap(ts.bad));
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
                (aux, Some(true))
            } else {
                (aux_latchs[i - 1], Some(false))
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
                if let Some(linit) = inits.get(&latchs[j]) {
                    init.push(Lit::new(latchs[(i - 1) * nl + j], *linit))
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
            let init = proof.rel.new_and(init);
            let p = proof.rel.new_and([!al, al_next]);
            let p = proof.rel.new_imply(p, init);
            bads.push(!p);
        }
        bads.push(!aux_latchs[0]);
        proof.bad = proof.rel.new_or(bads);
        assert!(proof.input.len() + proof.latch.len() == sum + k);
        Proof { proof }
    }

    fn witness(&mut self, _ts: &Transys) -> Witness {
        let mut wit = Witness::default();
        for l in self.uts.ts.latch() {
            let l = l.lit();
            if let Some(v) = self.solver.sat_value(l)
                && let Some(r) = self.uts.ts.restore(l.not_if(!v))
            {
                wit.init.push(r);
            }
        }
        for k in 0..=self.uts.num_unroll {
            let mut w = LitVec::new();
            for l in self.uts.ts.input() {
                let l = l.lit();
                let kl = self.uts.lit_next(l, k);
                if let Some(v) = self.solver.sat_value(kl)
                    && let Some(r) = self.uts.ts.restore(l.not_if(!v))
                {
                    w.push(r);
                }
            }
            wit.wit.push(w);
        }
        wit
    }
}
