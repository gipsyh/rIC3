mod bsq;
mod solver;

use crate::{options::Options, transys::Transys, verify::witness_encode, Engine};
use bsq::{BadState, BadStateQueue};
use logic_form::{Cube, Lemma};
use satif::Satif;
use solver::{DeepSolver, Lift};
use std::rc::Rc;

pub struct Deep {
    ts: Rc<Transys>,
    bs: Vec<Cube>,
    bsq: BadStateQueue,
    solver: DeepSolver,
    lift: Lift,
    options: Options,
}

impl Deep {
    pub fn new(options: Options, ts: Transys) -> Self {
        let ts = Rc::new(ts);
        let solver = DeepSolver::new(&ts);
        let lift = Lift::new(&ts);
        Self {
            ts,
            bs: Vec::new(),
            bsq: BadStateQueue::new(),
            solver,
            lift,
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
        self.bs.push(bad.clone());
        let cls = !&bad;
        self.solver.add_clause(&cls);
        let bad = Lemma::new(bad);
        if self.options.verbose > 1 {
            println!("depth: {depth}, bad: {bad}");
        }
        let init = self.ts.cube_subsume_init(&bad);
        self.bsq.add(BadState::new(bad, input, depth, next));
        if init {
            None
        } else {
            Some(())
        }
    }

    pub fn search(&mut self) -> Option<()> {
        while let Some(bad) = self.bsq.pop() {
            let bp = self.ts.cube_next(&bad.lemma);
            dbg!(bad.depth);
            if self.solver.solve(&bp) {
                let (nb, input) = self.get_predecessor(&bp);
                self.add_bad(nb, input, bad.depth + 1, Some(bad.clone()))?;
                self.bsq.add(bad);
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
