use crate::{
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf},
};
use giputils::bitvec::BitVec;
use logicrs::{LitVec, Var, VarBitVec, satif::Satif};
use rand::{Rng, SeedableRng, rngs::StdRng};

impl Transys {
    // fn random_fill(&self, sim: &mut VarBitVec, num_word: usize) {
    //     let mut rng = StdRng::seed_from_u64(0);
    //     while sim.bv_len() < num_word * BitVec::WORD_SIZE {
    //         let s = rng.random_range(0..sim.bv_len());
    //         sim[Var::CONST].push(false);
    //         for &v in self.latch.iter() {
    //             if !sim[v].is_empty() {
    //                 let b = sim[v].get(s);
    //                 sim[v].push(b);
    //             }
    //         }
    //     }
    //     let mut xstate: GHashSet<u64> = GHashSet::new();
    //     for &v in self.latch.iter() {
    //         if sim[v].is_empty() {
    //             for _ in 0..num_word {
    //                 let mut r: u64;
    //                 loop {
    //                     r = rng.random();
    //                     if !xstate.contains(&r) {
    //                         xstate.insert(r);
    //                         break;
    //                     }
    //                 }
    //                 sim[v].push_word(r);
    //             }
    //         }
    //         assert!(sim[v].len() == num_word * BitVec::WORD_SIZE);
    //     }
    // }

    fn state_assign(&self, sim: &VarBitVec, idx: usize) -> LitVec {
        let mut assump = LitVec::new();
        for &v in self.latch.iter() {
            if sim[v].is_empty() {
                continue;
            }
            let b = sim[v].get(idx);
            let l = v.lit().not_if(!b);
            assump.push(l);
        }
        assump
    }

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
        assert!(sim.bv_len() > 0);
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
            let block = !self.state_assign(init, i);
            let block = self.lits_next(block.iter());
            slv.add_clause(&block);
        }
        let domain: Vec<_> = self.next.values().map(|l| l.var()).collect();
        let mut rng = StdRng::seed_from_u64(0);
        let mut num_fail = 0;
        while sim.bv_len() < BitVec::WORD_SIZE {
            let from = rng.random_range(0..init.bv_len());
            let assump = self.state_assign(&init, from);
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
                let n = self.next(v.lit()).unwrap();
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
            let assump = self.state_assign(&sim, from);
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
                let n = self.next(v.lit()).unwrap();
                let va = slv.sat_value(n).unwrap();
                let na = slv.sat_value_lit(n.var()).unwrap();
                sim[v].push(va);
                block.push(!na);
            }
            slv.add_clause(&block);
        }
        sim
    }
}
