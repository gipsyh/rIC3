#![allow(non_snake_case)]
#![feature(assert_matches, get_mut_unchecked, format_args_nl)]

mod activity;
pub mod bmc;
mod frame;
pub mod frontend;
pub mod general;
mod gipsat;
pub mod imc;
pub mod kind;
mod mic;
pub mod options;
mod parallel;
pub mod portfolio;
mod proofoblig;
mod statistic;
pub mod transys;
pub mod verify;
pub mod wl;

use crate::proofoblig::{ProofObligation, ProofObligationQueue};
use crate::statistic::Statistic;
use activity::Activity;
use aig::{Aig, AigEdge};
use frame::{Frame, Frames};
use gipsat::statistic::SolverStatistic;
use gipsat::{Solver, Solvers};
use giputils::grc::Garc;
use logic_form::{Clause, Cube, Lemma, Lit, Var};
use options::Options;
use parallel::Worker;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Instant;
use transys::unroll::TransysUnroll;
use transys::Transys;
use verify::witness_encode;

pub trait Engine {
    fn check(&mut self) -> Option<bool>;

    fn certifaiger(&mut self, _aig: &Aig) -> Aig {
        panic!("unsupport certifaiger");
    }

    fn witness(&mut self, _aig: &Aig) -> String {
        panic!("unsupport witness");
    }

    fn statistic(&mut self) {}
}

pub struct IC3 {
    options: Options,
    ts: Rc<Transys>,
    frame: Frames,
    solvers: Vec<Solvers>,
    lift: Solver,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    pre_lemmas: Vec<Clause>,
    abs_cst: Cube,
    bmc_solver: Option<(Box<dyn satif::Satif>, TransysUnroll)>,

    auxiliary_var: Vec<Var>,
    xor_var: HashMap<(Lit, Lit), Lit>,
    workers: Vec<Garc<Worker>>,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        let new_solver = || {
            let mut solver = Solver::new(
                self.options.clone(),
                Some(self.frame.len()),
                &self.ts,
                &self.frame,
            );
            for v in self.auxiliary_var.iter() {
                solver.add_domain(*v, true);
            }
            solver
        };
        self.solvers
            .push(Solvers::new(new_solver, self.options.ic3.parallelism));
        self.frame.push(Frame::new());
        if self.level() == 0 {
            for init in self.ts.init.clone() {
                self.add_lemma(0, Cube::from([!init]), true, None);
            }
            let mut init = Cube::new();
            for l in self.ts.latchs.iter() {
                if self.ts.init_map[*l].is_none() {
                    if let Some(v) = self.solvers[0].sat_value(l.lit()) {
                        let l = l.lit().not_if(!v);
                        init.push(l);
                    }
                }
            }
            let ts = unsafe { Rc::get_mut_unchecked(&mut self.ts) };
            for i in init {
                ts.add_init(i.var(), Some(i.polarity()));
            }
        } else if self.level() == 1 {
            for cls in self.pre_lemmas.clone().iter() {
                self.add_lemma(1, !cls.clone(), true, None);
            }
        }
    }

    fn push_lemma(&mut self, frame: usize, mut cube: Cube) -> (usize, Cube) {
        let start = Instant::now();
        for i in frame + 1..=self.level() {
            if let Some(true) = self.solvers[i - 1].inductive(&cube, true, false) {
                cube = self.solvers[i - 1].inductive_core();
            } else {
                return (i, cube);
            }
        }
        self.statistic.block_push_time += start.elapsed();
        (self.level() + 1, cube)
    }

    fn generalize(&mut self, mut po: ProofObligation) -> bool {
        if self.options.ic3.inn && self.ts.cube_subsume_init(&po.lemma) {
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.lemma.cube().clone(), false, Some(po));
        }
        let mut mic = self.solvers[po.frame - 1].inductive_core();
        let level = if self.options.ic3.ctg { 1 } else { 0 };
        mic = if self.options.ic3.parallelism == 1 {
            self.mic(po.frame, mic, level, &[])
        } else {
            self.parallel_mic(po.frame, mic)
        };
        let (frame, mic) = self.push_lemma(po.frame, mic);
        self.statistic.avg_po_cube_len += po.lemma.len();
        po.frame = frame;
        self.add_obligation(po.clone());
        if self.add_lemma(frame - 1, mic.clone(), false, Some(po)) {
            return true;
        }
        if self.options.ic3.xor {
            self.xor_generalize2(frame - 1, mic);
        }
        false
    }

    fn block(&mut self) -> Option<bool> {
        while let Some(mut po) = self.obligations.pop(self.level()) {
            if po.removed {
                continue;
            }
            if self.ts.cube_subsume_init(&po.lemma) {
                if self.options.ic3.abs_cst {
                    self.add_obligation(po.clone());
                    if let Some(c) = self.check_witness_by_bmc(po.clone()) {
                        for c in c {
                            assert!(!self.abs_cst.contains(&c));
                            self.abs_cst.push(c);
                        }
                        if self.options.verbose > 1 {
                            println!("abs cst len: {}", self.abs_cst.len(),);
                        }
                        self.obligations.clear();
                        for f in self.frame.iter_mut() {
                            for l in f.iter_mut() {
                                l.po = None;
                            }
                        }
                        continue;
                    } else {
                        return Some(false);
                    }
                } else if self.options.ic3.inn && po.frame > 0 {
                    assert!(!self.solvers[0]
                        .solve_with_domain(&po.lemma, vec![], true, false)
                        .unwrap());
                } else {
                    self.add_obligation(po.clone());
                    assert!(po.frame == 0);
                    return Some(false);
                }
            }
            if let Some((bf, _)) = self.frame.trivial_contained(po.frame, &po.lemma) {
                po.frame = bf + 1;
                self.add_obligation(po);
                continue;
            }
            if self.options.verbose > 2 {
                self.frame.statistic();
            }
            let blocked_start = Instant::now();
            let blocked = self
                .blocked_with_ordered(po.frame, &po.lemma, false, false, false)
                .unwrap();
            self.statistic.block_blocked_time += blocked_start.elapsed();
            if blocked {
                if self.generalize(po) {
                    return None;
                }
            } else {
                let (model, inputs) = self.get_predecessor(po.frame, true);
                self.add_obligation(ProofObligation::new(
                    po.frame - 1,
                    Lemma::new(model),
                    inputs,
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.add_obligation(po);
            }
        }
        Some(true)
    }

    #[allow(unused)]
    fn trivial_block(
        &mut self,
        frame: usize,
        lemma: Lemma,
        constrain: &[Clause],
        limit: &mut usize,
        level: usize,
    ) -> bool {
        assert!(level == 0);
        if frame == 0 {
            return false;
        }
        if self.ts.cube_subsume_init(&lemma) {
            return false;
        }
        if *limit == 0 {
            return false;
        }
        *limit -= 1;
        loop {
            if self
                .blocked_with_ordered_with_constrain(
                    frame,
                    &lemma,
                    false,
                    true,
                    constrain.to_vec(),
                    false,
                )
                .unwrap()
            {
                let mut mic = self.solvers[frame - 1].inductive_core();
                mic = self.mic(frame, mic, level, constrain);
                let (frame, mic) = self.push_lemma(frame, mic);
                self.add_lemma(frame - 1, mic, false, None);
                return true;
            } else {
                let model = Lemma::new(self.get_predecessor(frame, true).0);
                if !self.trivial_block(frame - 1, model, constrain, limit, level) {
                    return false;
                }
            }
        }
    }

    fn propagate(&mut self) -> bool {
        for frame_idx in self.frame.early..self.level() {
            self.frame[frame_idx].sort_by_key(|x| x.len());
            let frame = self.frame[frame_idx].clone();
            for mut lemma in frame {
                if self.frame[frame_idx].iter().all(|l| l.ne(&lemma)) {
                    continue;
                }
                for ctp in 0..3 {
                    if self
                        .blocked_with_ordered(frame_idx + 1, &lemma, false, false, false)
                        .unwrap()
                    {
                        let core = if self.options.ic3.inn && self.ts.cube_subsume_init(&lemma) {
                            lemma.cube().clone()
                        } else {
                            self.solvers[frame_idx].inductive_core()
                        };
                        if let Some(po) = &mut lemma.po {
                            if po.frame < frame_idx + 2 && self.obligations.remove(po) {
                                po.frame = frame_idx + 2;
                                self.obligations.add(po.clone());
                            }
                        }
                        self.add_lemma(frame_idx + 1, core, true, lemma.po);
                        self.statistic.ctp.statistic(ctp > 0);
                        break;
                    }
                    if !self.options.ic3.ctp {
                        break;
                    }
                    let (ctp, _) = self.get_predecessor(frame_idx + 1, false);
                    if !self.ts.cube_subsume_init(&ctp)
                        && self.solvers[frame_idx - 1]
                            .inductive(&ctp, true, false)
                            .unwrap()
                    {
                        let core = self.solvers[frame_idx - 1].inductive_core();
                        let mic = self.mic(frame_idx, core, 0, &[]);
                        if self.add_lemma(frame_idx, mic, false, None) {
                            return true;
                        }
                    } else {
                        break;
                    }
                }
            }
            if self.frame[frame_idx].is_empty() {
                return true;
            }
        }
        self.frame.early = self.level();
        false
    }
}

impl IC3 {
    pub fn new(options: Options, mut ts: Transys, pre_lemmas: Vec<Clause>) -> Self {
        if options.ic3.inn {
            let mut uts = TransysUnroll::new(&ts);
            uts.unroll();
            ts = uts.interal_signals();
            ts = ts.simplify(&[], true, false);
        }
        let ts = Rc::new(ts);
        let statistic = Statistic::new(&options.model);
        let activity = Activity::new(&ts);
        let frame = Frames::new(&ts);
        let lift = Solver::new(options.clone(), None, &ts, &frame);
        let abs_cst = if options.ic3.abs_cst {
            Cube::new()
        } else {
            ts.constraints.clone()
        };
        let mut res = Self {
            options,
            ts,
            activity,
            solvers: Vec::new(),
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
            abs_cst,
            pre_lemmas,
            auxiliary_var: Vec::new(),
            xor_var: HashMap::new(),
            bmc_solver: None,
            workers: Default::default(),
        };
        res.extend();
        res
    }
}

impl Engine for IC3 {
    fn check(&mut self) -> Option<bool> {
        self.create_workers();
        loop {
            let start = Instant::now();
            loop {
                match self.block() {
                    Some(false) => {
                        self.statistic.overall_block_time += start.elapsed();
                        self.statistic();
                        return Some(false);
                    }
                    None => {
                        self.statistic.overall_block_time += start.elapsed();
                        self.statistic();
                        self.verify();
                        return Some(true);
                    }
                    _ => (),
                }
                if let Some((bad, inputs)) = self.get_bad() {
                    let bad = Lemma::new(bad);
                    self.add_obligation(ProofObligation::new(self.level(), bad, inputs, 0, None))
                } else {
                    break;
                }
            }
            let blocked_time = start.elapsed();
            if self.options.verbose > 1 {
                self.frame.statistic();
                println!(
                    "[{}:{}] frame: {}, time: {:?}",
                    file!(),
                    line!(),
                    self.level(),
                    blocked_time,
                );
            }
            self.statistic.overall_block_time += blocked_time;
            self.extend();
            let start = Instant::now();
            let propagate = if self.options.ic3.parallelism > 1 {
                self.parallel_propagate()
            } else {
                self.propagate()
            };
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
                self.statistic();
                self.verify();
                return Some(true);
            }
        }
    }

    fn certifaiger(&mut self, aig: &Aig) -> Aig {
        let invariants = self.frame.invariant();
        let invariants = invariants
            .iter()
            .map(|l| Cube::from_iter(l.iter().map(|l| self.ts.restore(*l))));
        let mut certifaiger = aig.clone();
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf
                .push(certifaiger.new_ands_node(cube.into_iter().map(AigEdge::from_lit)));
        }
        let invariants = certifaiger.new_ors_node(certifaiger_dnf.into_iter());
        let constrains: Vec<AigEdge> = certifaiger.constraints.iter().map(|e| !*e).collect();
        let constrains = certifaiger.new_ors_node(constrains.into_iter());
        let invariants = certifaiger.new_or_node(invariants, constrains);
        certifaiger.bads.clear();
        certifaiger.outputs.clear();
        certifaiger.outputs.push(invariants);
        certifaiger
    }

    fn witness(&mut self, aig: &Aig) -> String {
        let mut res: Vec<Cube> = vec![Cube::new()];
        if let Some((bmc_solver, uts)) = self.bmc_solver.as_mut() {
            let mut wit = vec![Cube::new()];
            for l in uts.ts.latchs.iter() {
                let l = l.lit();
                if let Some(v) = bmc_solver.sat_value(l) {
                    wit[0].push(uts.ts.restore(l.not_if(!v)));
                }
            }
            for k in 0..=uts.num_unroll {
                let mut w = Cube::new();
                for l in uts.ts.inputs.iter() {
                    let l = l.lit();
                    let kl = uts.lit_next(l, k);
                    if let Some(v) = bmc_solver.sat_value(kl) {
                        w.push(uts.ts.restore(l.not_if(!v)));
                    }
                }
                wit.push(w);
            }
            return witness_encode(aig, &wit);
        }
        let b = self.obligations.peak().unwrap();
        assert!(b.frame == 0);
        let mut assump = if let Some(next) = b.next.clone() {
            self.ts.cube_next(&next.lemma)
        } else {
            self.ts.bad.clone()
        };
        assump.extend_from_slice(&b.input);
        assert!(self.solvers[0]
            .solve_with_domain(&assump, vec![], false, false)
            .unwrap());
        for l in self.ts.latchs.iter() {
            let l = l.lit();
            if let Some(v) = self.solvers[0].sat_value(l) {
                res[0].push(self.ts.restore(l.not_if(!v)));
            }
        }
        let mut b = Some(b);
        while let Some(bad) = b {
            res.push(bad.input.iter().map(|l| self.ts.restore(*l)).collect());
            b = bad.next.clone();
        }
        witness_encode(aig, &res)
    }

    fn statistic(&mut self) {
        if self.options.verbose > 0 {
            self.statistic.num_auxiliary_var = self.auxiliary_var.len();
            self.obligations.statistic();
            for f in self.frame.iter() {
                print!("{} ", f.len());
            }
            println!();
            let mut statistic = SolverStatistic::default();
            for s in self.solvers.iter() {
                // for s in s.iter() {
                statistic += s.statistic;
                // }
            }
            println!("{:#?}", statistic);
            println!("{:#?}", self.statistic);
        }
    }
}
