use crate::{
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf},
};
use giputils::bitvec::BitVec;
use logicrs::{LitVec, Var, VarBitVec, satif::Satif};
use rand::{Rng, SeedableRng, rngs::StdRng};

struct Simulate<'t> {
    ts: &'t Transys,
    sim: VarBitVec,
    slv: DagCnfSolver,
    consider: Vec<Var>,
    num_word: usize,
    domain: Vec<Var>,
    _rng: StdRng,
}

impl Simulate<'_> {
    fn rt_dfs_simulate(&mut self, from: usize) {
        let assump = self.sim.assign(from, Some(self.consider.iter().copied()));
        loop {
            if self.sim.bv_len() >= self.num_word * BitVec::WORD_SIZE {
                return;
            }
            self.slv.clear_phase();
            if !self
                .slv
                .solve_with_param(&assump, vec![], self.domain.iter().copied(), Some(5))
                .is_some_and(|r| r)
            {
                return;
            }
            self.sim[Var::CONST].push(false);
            let mut block = LitVec::new();
            for &v in self.consider.iter() {
                let n = self.ts.next(v.lit());
                let va = self.slv.sat_value(n).unwrap();
                let na = self.slv.sat_value_lit(n.var()).unwrap();
                self.sim[v].push(va);
                block.push(!na);
            }
            self.slv.add_clause(&block);
            self.rt_dfs_simulate(self.sim.bv_len() - 1);
        }
    }
}

impl Transys {
    pub fn init_simulation(&self, num_word: usize) -> VarBitVec {
        let mut slv = DagCnfSolver::new(&self.rel);
        for cls in self.constraint() {
            slv.add_clause(&cls.cube());
        }
        self.load_init(&mut slv);
        let mut sim = VarBitVec::new();
        sim.reserve(self.max_var());
        while sim.bv_len() < num_word * BitVec::WORD_SIZE {
            slv.clear_phase();
            if !slv.solve(&[]) {
                break;
            }
            sim[Var::CONST].push(false);
            let mut block = LitVec::new();
            for &v in self.latch.iter() {
                if let Some(a) = slv.sat_value(v.lit()) {
                    block.push(!slv.sat_value_lit(v).unwrap());
                    sim[v].push(a);
                } else {
                    sim[v].clear();
                }
            }
            slv.add_clause(&block);
        }
        sim
    }

    pub fn rt_simulation(&self, init: &VarBitVec, num_word: usize) -> VarBitVec {
        assert!(init.bv_len() > 0);
        let mut sim = VarBitVec::new();
        sim.reserve(self.max_var());
        let mut slv = DagCnfSolver::new(&self.rel);
        for cls in self.constraint() {
            slv.add_clause(&cls.cube());
        }
        for i in 0..init.bv_len() {
            let block = !init.assign(i, Some(self.latch().filter(|v| !init[*v].is_empty())));
            let block = self.lits_next(block.iter());
            slv.add_clause(&block);
        }
        let domain: Vec<_> = self.next.values().map(|l| l.var()).collect();
        let mut rng = StdRng::seed_from_u64(0);
        let mut num_fail = 0;
        while sim.bv_len() < BitVec::WORD_SIZE {
            let from = rng.random_range(0..init.bv_len());
            let assump = init.assign(from, Some(self.latch().filter(|v| !init[*v].is_empty())));
            slv.clear_phase();
            if !slv.solve_with_domain(&assump, domain.iter().copied()) {
                num_fail += 1;
                if num_fail > 100 {
                    break;
                }
                continue;
            }
            sim[Var::CONST].push(false);
            let mut block = LitVec::new();
            for &v in self.latch.iter() {
                let n = self.next(v.lit());
                let va = slv.sat_value(n).unwrap();
                let na = slv.sat_value_lit(n.var()).unwrap();
                sim[v].push(va);
                block.push(!na);
            }
            slv.add_clause(&block);
        }
        num_fail = 0;
        while sim.bv_len() < num_word * BitVec::WORD_SIZE {
            let from = rng.random_range(0..sim.bv_len());
            let assump = sim.assign(from, Some(self.latch()));
            slv.clear_phase();
            if !slv.solve_with_domain(&assump, domain.iter().copied()) {
                num_fail += 1;
                if num_fail > 100 {
                    break;
                }
                continue;
            }
            sim[Var::CONST].push(false);
            let mut block = LitVec::new();
            for &v in self.latch.iter() {
                let n = self.next(v.lit());
                let va = slv.sat_value(n).unwrap();
                let na = slv.sat_value_lit(n.var()).unwrap();
                sim[v].push(va);
                block.push(!na);
            }
            slv.add_clause(&block);
        }
        sim
    }

    pub fn rt_simulation2(&self, init: &VarBitVec, num_word: usize) -> VarBitVec {
        assert!(init.bv_len() > 0);
        let mut sim = VarBitVec::new();
        let consider: Vec<_> = self.latch().filter(|v| !init[*v].is_empty()).collect();
        sim.reserve(self.max_var());
        let mut slv = DagCnfSolver::new(&self.rel);
        for cls in self.constraint() {
            slv.add_clause(&cls.cube());
        }
        for i in 0..init.bv_len() {
            let block = !init.assign(i, Some(consider.iter().copied()));
            let block = self.lits_next(block.iter());
            slv.add_clause(&block);
        }
        let domain: Vec<_> = self.next.values().map(|l| l.var()).collect();
        let mut simulate = Simulate {
            ts: self,
            sim,
            slv,
            num_word,
            domain,
            consider,
            _rng: StdRng::seed_from_u64(0),
        };

        for from in 0..init.bv_len() {
            let assump = init.assign(from, Some(self.latch().filter(|v| !init[*v].is_empty())));
            loop {
                if simulate.sim.bv_len() >= num_word * BitVec::WORD_SIZE {
                    return simulate.sim;
                }
                if !simulate
                    .slv
                    .solve_with_domain(&assump, simulate.domain.iter().copied())
                {
                    break;
                }
                simulate.sim[Var::CONST].push(false);
                let mut block = LitVec::new();
                for &v in simulate.consider.iter() {
                    let n = simulate.ts.next(v.lit());
                    let va = simulate.slv.sat_value(n).unwrap();
                    let na = simulate.slv.sat_value_lit(n.var()).unwrap();
                    simulate.sim[v].push(va);
                    block.push(!na);
                }
                simulate.slv.add_clause(&block);
                simulate.rt_dfs_simulate(simulate.sim.bv_len() - 1);
            }
        }
        simulate.sim
    }
}
