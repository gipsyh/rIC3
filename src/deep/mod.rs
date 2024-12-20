mod bsq;
mod mic;

use crate::{
    gipsat,
    options::Options,
    transys::{unroll::TransysUnroll, Transys},
    verify::witness_encode,
    Engine,
};
use bsq::{BadState, BadStateQueue};
use logic_form::{Cube, Lemma};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};
use std::rc::Rc;

pub struct Deep {
    ts: Rc<Transys>,
    unroll: Rc<Transys>,
    bsq: BadStateQueue,
    solver: gipsat::Solver,
    bad_solver: gipsat::Solver,
    lift: gipsat::Solver,
    bad_lift: gipsat::Solver,
    options: Options,
    rng: StdRng,
}

impl Deep {
    pub fn new(options: Options, ts: Transys) -> Self {
        let ts = Rc::new(ts);
        let mut unroll = TransysUnroll::new(&ts);
        unroll.unroll();
        let unroll = Rc::new(unroll.compile());
        let mut solver = gipsat::Solver::new(options.clone(), Some(0), &ts);
        let mut bad_solver = gipsat::Solver::new(options.clone(), Some(0), &unroll);
        solver.add_lemma(&[!ts.bad[0]]);
        bad_solver.add_lemma(&[!ts.bad[0]]);
        let lift = gipsat::Solver::new(options.clone(), None, &ts);
        let bad_lift = gipsat::Solver::new(options.clone(), None, &unroll);
        let rng = StdRng::seed_from_u64(options.rseed);
        Self {
            ts,
            unroll,
            bsq: BadStateQueue::new(),
            solver,
            bad_solver,
            lift,
            bad_lift,
            rng,
            options,
        }
    }

    pub fn add_bad(
        &mut self,
        bad: Cube,
        input: Cube,
        depth: usize,
        next: Option<BadState>,
    ) -> Option<()> {
        let cls = !&bad;
        self.solver.add_lemma(&cls);
        self.bad_solver.add_lemma(&cls);
        let bad = Lemma::new(bad);
        if self.options.verbose > 1 {
            print!("depth: {depth}");
            if self.options.verbose > 2 {
                print!(", bad: {bad}")
            }
            println!()
        }
        let init = self.ts.cube_subsume_init(&bad);
        self.bsq.add(BadState::new(bad, input, depth, next));
        if init {
            None
        } else {
            Some(())
        }
    }

    pub fn get_bad(&mut self) -> Option<(Cube, Cube)> {
        self.bad_solver.assump = self.unroll.bad.clone();
        self.bad_solver.constrain = Default::default();
        let res = self
            .bad_solver
            .solve_with_domain(&self.unroll.bad, vec![], false);
        if res {
            Some(self.bad_lift.get_pred(&mut self.bad_solver, true))
        } else {
            None
        }
    }

    pub fn search(&mut self) -> Option<()> {
        while let Some(bad) = self.bsq.pop() {
            if !self.solver.inductive(&bad.lemma, false) {
                let (nb, input) = self.lift.get_pred(&mut self.solver, true);
                self.add_bad(nb, input, bad.depth + 1, Some(bad.clone()))?;
                self.bsq.add(bad);
            } else {
                let mut core = self.solver.inductive_core();
                loop {
                    core.shuffle(&mut self.rng);
                    assert!(self.solver.inductive(&core, true));
                    let nc = self.solver.inductive_core();
                    if nc.len() == core.len() {
                        break;
                    }
                    core = nc;
                }
                // let cl = core.len();
                let core = self.mic(core);
                self.solver.add_lemma(&!&core);
                self.bad_solver.add_lemma(&!&core);
                // dbg!(cl - nc.len());
            }
        }
        Some(())
    }
}

impl Engine for Deep {
    fn check(&mut self) -> Option<bool> {
        while let Some((bad, input)) = self.get_bad() {
            if self.add_bad(bad, input, 1, None).is_none() {
                return Some(false);
            }
            if self.search().is_none() {
                return Some(false);
            }
        }
        Some(true)
    }

    fn witness(&mut self, aig: &aig::Aig) -> String {
        let mut res: Vec<Cube> = vec![Cube::new()];
        let b = self.bsq.peak().unwrap();
        res[0] = b.lemma.iter().map(|l| self.ts.restore(*l)).collect();
        let mut b = Some(b);
        while let Some(bad) = b {
            res.push(bad.input.iter().map(|l| self.ts.restore(*l)).collect());
            b = bad.next.clone();
        }
        witness_encode(aig, &res)
    }
}
