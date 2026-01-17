use logicrs::{Lit, LitVec, LitVvec, Var, VarRange, satif::Satif};
use rIC3::{
    Engine, McProof, McResult, McWitness,
    transys::{
        Transys, TransysIf,
        certify::{BlProof, BlWitness, Restore},
        unroll::TransysUnroll,
    },
};

pub struct CIllKind {
    prop: usize,
    uts: TransysUnroll<Transys>,
    solver: Box<dyn Satif>,
    slv_trans_k: usize,
    slv_bad_k: usize,
    local_cst: LitVvec,
    wit_assume: Option<BlWitness>,
    ots: Transys,
    rst: Restore,
}

impl CIllKind {
    pub fn new(
        prop: usize,
        ts: Transys,
        local_cst: LitVvec,
        wit_assume: Option<BlWitness>,
    ) -> Self {
        let ots = ts.clone();
        let rst = Restore::new(&ts);
        assert!(!ts.has_gate_init());
        let mut uts = TransysUnroll::new(&ts);
        uts.enable_simple_path();
        let solver: Box<dyn Satif> = Box::new(cadical::CaDiCaL::new());
        Self {
            prop,
            uts,
            solver,
            slv_trans_k: 0,
            slv_bad_k: 0,
            ots,
            rst,
            local_cst,
            wit_assume,
        }
    }

    fn load_trans_to(&mut self, k: usize) {
        while self.slv_trans_k < k + 1 {
            self.uts
                .load_trans(self.solver.as_mut(), self.slv_trans_k, true);
            self.slv_trans_k += 1;
        }
    }

    fn load_bad_to(&mut self, k: usize) {
        while self.slv_bad_k < k + 1 {
            for b in self.uts.lits_next(&self.uts.ts.bad, self.slv_bad_k) {
                self.solver.add_clause(&[!b]);
            }
            for c in self.local_cst.iter() {
                let c: LitVec = c.iter().map(|l| self.rst.forward(*l)).collect();
                let c: LitVec = self.uts.lits_next(c, self.slv_bad_k).collect();
                self.solver.add_clause(&!c);
            }
            self.slv_bad_k += 1;
        }
    }

    fn load_witness_assume(&mut self) {
        let Some(wit) = &self.wit_assume else {
            return;
        };
        assert!(wit.len() == self.uts.num_unroll + 1);
        for k in 0..=self.uts.num_unroll {
            for l in self
                .uts
                .lits_next(wit.input[k].iter().chain(wit.state[k].iter()), k)
            {
                self.solver.add_clause(&[l]);
            }
        }
    }
}

impl Engine for CIllKind {
    fn check(&mut self) -> McResult {
        let k = 3;
        self.uts.unroll_to(k);
        self.load_trans_to(k);
        self.load_witness_assume();
        self.load_bad_to(k - 1);
        let bad = self.uts.lit_next(self.uts.ts.bad[self.prop], k);
        let res = self.solver.solve(&[bad]);
        if !res {
            return McResult::Safe;
        }
        McResult::Unknown(Some(k))
    }

    fn proof(&mut self) -> McProof {
        let mut ts = self.ots.clone();
        let eqi = self.rst.eq_invariant();
        let mut certifaiger_dnf = vec![];
        for cube in eqi {
            certifaiger_dnf.push(ts.rel.new_and(cube));
        }
        for lc in self.local_cst.iter() {
            certifaiger_dnf.push(ts.rel.new_and(lc));
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
            for v in VarRange::new_inclusive(Var(1), ts.max_var()) {
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
        let f = |k: usize| {
            if k < self.uts.num_unroll {
                !&self.uts.ts.bad
            } else {
                LitVec::new()
            }
        };
        wit.bad_id = self.prop;
        wit.lift(&self.uts, Some(f));
        wit = self.rst.restore_witness(&wit);
        McWitness::Bl(wit)
    }
}
