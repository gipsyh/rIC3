use super::{IC3, proofoblig::ProofObligation};
use crate::{gipsat::TransysSolver, transys::TransysCtx};
use giputils::grc::Grc;
use giputils::hash::GHashSet;
use logicrs::{Lit, LitOrdVec, LitSet, LitVec, Var, satif::Satif};
use std::{
    fmt::Write,
    ops::{Deref, DerefMut},
};

#[derive(Clone)]
pub struct FrameLemma {
    lemma: LitOrdVec,
    pub po: Option<ProofObligation>,
    pub _ctp: Option<LitVec>,
}

impl FrameLemma {
    #[inline]
    pub fn new(lemma: LitOrdVec, po: Option<ProofObligation>, ctp: Option<LitVec>) -> Self {
        Self {
            lemma,
            po,
            _ctp: ctp,
        }
    }
}

impl Deref for FrameLemma {
    type Target = LitOrdVec;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.lemma
    }
}

impl DerefMut for FrameLemma {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lemma
    }
}

#[derive(Default)]
pub struct Frame {
    lemmas: Vec<FrameLemma>,
}

impl Frame {
    pub fn new() -> Self {
        Self { lemmas: Vec::new() }
    }
}

impl Deref for Frame {
    type Target = Vec<FrameLemma>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.lemmas
    }
}

impl DerefMut for Frame {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lemmas
    }
}

pub struct Frames {
    frames: Vec<Frame>,
    pub inf: Frame,
    pub early: usize,
    pub tmp_lit_set: LitSet,
}

impl Frames {
    pub fn new(ts: &Grc<TransysCtx>) -> Self {
        let mut tmp_lit_set = LitSet::new();
        tmp_lit_set.reserve(ts.max_latch);
        Self {
            frames: Default::default(),
            inf: Default::default(),
            early: 1,
            tmp_lit_set,
        }
    }

    pub fn reserve(&mut self, var: Var) {
        self.tmp_lit_set.reserve(var);
    }

    #[inline]
    pub fn trivial_contained<'a>(
        &'a mut self,
        frame: Option<usize>,
        lemma: &LitOrdVec,
    ) -> Option<(Option<usize>, &'a mut Option<ProofObligation>)> {
        for l in lemma.iter() {
            self.tmp_lit_set.insert(*l);
        }
        if let Some(frame) = frame {
            for (i, fi) in self.frames.iter_mut().enumerate().skip(frame) {
                for j in 0..fi.len() {
                    if fi[j].lemma.subsume_set(lemma, &self.tmp_lit_set) {
                        self.tmp_lit_set.clear();
                        return Some((Some(i), &mut fi[j].po));
                    }
                }
            }
        }
        for j in 0..self.inf.len() {
            if self.inf[j].lemma.subsume_set(lemma, &self.tmp_lit_set) {
                self.tmp_lit_set.clear();
                return Some((None, &mut self.inf[j].po));
            }
        }
        self.tmp_lit_set.clear();
        None
    }

    pub fn parent_lemma(&self, lemma: &[Lit], frame: usize) -> Option<LitOrdVec> {
        if frame == 1 {
            return None;
        }
        let lemma = LitOrdVec::new(LitVec::from(lemma));
        for c in self.frames[frame - 1].iter() {
            if c.subsume(&lemma) {
                return Some(c.lemma.clone());
            }
        }
        None
    }

    pub fn _parent_lemmas(&self, lemma: &LitOrdVec, frame: usize) -> Vec<LitOrdVec> {
        let mut res = Vec::new();
        if frame == 1 {
            return res;
        }
        for c in self.frames[frame - 1].iter() {
            if c.subsume(lemma) {
                res.push(c.lemma.clone());
            }
        }
        res
    }

    #[allow(unused)]
    pub fn similar(&self, cube: &[Lit], frame: usize) -> Vec<LitVec> {
        let cube_set: GHashSet<Lit> = GHashSet::from_iter(cube.iter().copied());
        let mut res = GHashSet::new();
        for frame in self.frames[frame..].iter() {
            for lemma in frame.iter() {
                let sec: LitVec = lemma
                    .iter()
                    .filter(|l| cube_set.contains(l))
                    .copied()
                    .collect();
                if sec.len() != cube.len() && sec.len() * 2 >= cube.len() {
                    res.insert(sec);
                }
            }
        }
        let mut res = Vec::from_iter(res);
        res.sort_by_key(|x| x.len());
        res.reverse();
        if res.len() > 3 {
            res.truncate(3);
        }
        res
    }

    #[inline]
    pub fn statistic(&self, compact: bool) -> String {
        let mut s = String::new();
        let total = self.frames.len() + 1;
        s.write_fmt(format_args!("frames [{total}]: ")).unwrap();
        let frames_iter: Box<dyn Iterator<Item = &Frame>> = if compact && total > 50 {
            s.push_str("... ");
            Box::new(self.frames.iter().skip(total - 50))
        } else {
            Box::new(self.frames.iter())
        };
        for f in frames_iter {
            s.write_fmt(format_args!("{} ", f.len())).unwrap();
        }
        s.write_fmt(format_args!("{} ", self.inf.len())).unwrap();
        s
    }
}

impl Deref for Frames {
    type Target = Vec<Frame>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.frames
    }
}

impl DerefMut for Frames {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}

impl Frames {
    #[inline]
    pub fn get_mut(&mut self) -> &mut Vec<Frame> {
        &mut self.frames
    }
}

impl IC3 {
    #[inline]
    pub(super) fn add_lemma(
        &mut self,
        frame: usize,
        lemma: LitVec,
        contained_check: bool,
        po: Option<ProofObligation>,
    ) -> bool {
        let lemma = LitOrdVec::new(lemma);
        if frame == 0 {
            assert!(self.frame.len() == 1);
            if self.level() == frame
                && let Some(predprop) = self.predprop.as_mut()
            {
                predprop.add_lemma(&lemma);
            }
            self.solvers[0].add_clause(&!lemma.as_litvec());
            self.frame[0].push(FrameLemma::new(lemma, po, None));
            return false;
        }
        if contained_check && self.frame.trivial_contained(Some(frame), &lemma).is_some() {
            return false;
        }
        let mut begin = None;
        let mut inv_found = false;
        'fl: for i in (1..=frame).rev() {
            let mut j = 0;
            while j < self.frame[i].len() {
                let l = &self.frame[i][j];
                if begin.is_none() && l.subsume(&lemma) {
                    if l.eq(&lemma) {
                        self.frame[i].swap_remove(j);
                        let clause = !lemma.as_litvec();
                        for k in i + 1..=frame {
                            self.solvers[k].add_clause(&clause);
                        }
                        if self.level() == frame
                            && let Some(predprop) = self.predprop.as_mut()
                        {
                            predprop.add_lemma(&lemma);
                        }
                        self.frame[frame].push(FrameLemma::new(lemma, po, None));
                        self.frame.early = self.frame.early.min(i + 1);
                        return self.frame[i].is_empty();
                    } else {
                        begin = Some(i + 1);
                        break 'fl;
                    }
                }
                if lemma.subsume(l) {
                    let _remove = self.frame[i].swap_remove(j);
                    // self.solvers[i].remove_lemma(&remove);
                    continue;
                }
                j += 1;
            }
            if i != frame && self.frame[i].is_empty() {
                inv_found = true;
            }
        }
        let clause = !lemma.as_litvec();
        let begin = begin.unwrap_or(1);
        for i in begin..=frame {
            self.solvers[i].add_clause(&clause);
        }
        if self.level() == frame
            && let Some(predprop) = self.predprop.as_mut()
        {
            predprop.add_lemma(&lemma);
        }
        self.frame[frame].push(FrameLemma::new(lemma, po, None));
        self.frame.early = self.frame.early.min(begin);
        inv_found
    }

    pub(super) fn add_inf_lemma(&mut self, lemma: LitVec) {
        let lemma = LitOrdVec::new(lemma);
        assert!(self.frame.trivial_contained(None, &lemma).is_none());
        let lastf = self.frame.last_mut().unwrap();
        let olen = lastf.len();
        lastf.retain(|l| !l.eq(&lemma));
        assert!(lastf.len() + 1 == olen);
        let clause = !lemma.as_litvec();
        self.inf_solver.add_clause(&clause);
        self.frame.inf.push(FrameLemma::new(lemma, None, None));
    }

    pub fn inner_invariant(&self) -> Vec<LitVec> {
        let mut invariants: Vec<_> = self
            .frame
            .inf
            .iter()
            .map(|c| c.as_litvec().clone())
            .collect();
        if let Some(invariant) = self.frame.iter().position(|frame| frame.is_empty()) {
            for i in invariant..self.frame.len() {
                for cube in self.frame[i].iter() {
                    invariants.push(cube.as_litvec().clone());
                }
            }
        } else {
            let mut cand: Vec<_> = self
                .frame
                .last()
                .unwrap()
                .iter()
                .map(|l| l.as_litvec().clone())
                .collect();
            loop {
                let mut slv = TransysSolver::new(&self.tsctx);
                for i in invariants.iter() {
                    slv.add_clause(&!i);
                }
                for c in cand.iter() {
                    slv.add_clause(&!c);
                }
                let mut new_cand = Vec::new();
                for c in cand.iter() {
                    if slv.inductive(c, false) {
                        new_cand.push(c.clone());
                    }
                }
                if new_cand.len() == cand.len() {
                    invariants.extend(new_cand);
                    break;
                } else {
                    cand = new_cand;
                }
            }
        }
        invariants
    }

    // pub fn remove_lemma(&mut self, frame: usize, lemmas: Vec<LitVec>) {
    //     let lemmas: GHashSet<LitOrdVec> = GHashSet::from_iter(lemmas.into_iter().map(LitOrdVec::new));
    //     for i in (1..=frame).rev() {
    //         let mut j = 0;
    //         while j < self.frame[i].len() {
    //             if let Some(po) = &mut self.frame[i][j].po {
    //                 po.removed = true;
    //             }
    //             if lemmas.contains(&self.frame[i][j]) {
    //                 for s in self.solvers[..=frame].iter_mut() {
    //                     s.remove_lemma(&self.frame[i][j]);
    //                 }
    //                 self.frame[i].swap_remove(j);
    //             } else {
    //                 j += 1;
    //             }
    //         }
    //     }
    // }
}
