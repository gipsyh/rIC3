use crate::{proofoblig::ProofObligation, IC3};
use logic_form::{Cube, Lemma, Lit, LitSet};
use std::{
    collections::HashSet,
    ops::{Deref, DerefMut},
    rc::Rc,
};
use transys::Transys;

#[derive(Clone)]
pub struct FrameLemma {
    lemma: Lemma,
    pub po: Option<ProofObligation>,
    pub _ctp: Option<Cube>,
}

impl FrameLemma {
    #[inline]
    pub fn new(lemma: Lemma, po: Option<ProofObligation>, ctp: Option<Cube>) -> Self {
        Self {
            lemma,
            po,
            _ctp: ctp,
        }
    }
}

impl Deref for FrameLemma {
    type Target = Lemma;

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

#[derive(Clone)]
pub struct Frames {
    frames: Rc<Vec<Frame>>,
    pub early: usize,
    pub tmp_lit_set: Rc<LitSet>,
}

impl Frames {
    pub fn new(ts: &Rc<Transys>) -> Self {
        let mut tmp_lit_set = LitSet::new();
        tmp_lit_set.reserve(ts.max_latch);
        Self {
            frames: Default::default(),
            early: 1,
            tmp_lit_set: Rc::new(tmp_lit_set),
        }
    }

    #[inline]
    pub fn trivial_contained<'a>(
        &'a mut self,
        frame: usize,
        lemma: &Lemma,
    ) -> Option<(usize, &'a mut Option<ProofObligation>)> {
        let tmp_lit_set = unsafe { Rc::get_mut_unchecked(&mut self.tmp_lit_set) };
        let frames = unsafe { Rc::get_mut_unchecked(&mut self.frames) };
        for l in lemma.iter() {
            tmp_lit_set.insert(*l);
        }
        for i in frame..frames.len() {
            for j in 0..frames[i].len() {
                if frames[i][j].lemma.subsume_set(lemma, tmp_lit_set) {
                    tmp_lit_set.clear();
                    return Some((i, &mut frames[i][j].po));
                }
            }
        }
        tmp_lit_set.clear();
        None
    }

    pub fn invariant(&self) -> Vec<Lemma> {
        let invariant = self.iter().position(|frame| frame.is_empty()).unwrap();
        let mut invariants = Vec::new();
        for i in invariant..self.len() {
            for cube in self[i].iter() {
                invariants.push(cube.deref().clone());
            }
        }
        invariants.sort();
        invariants
    }

    pub fn _parent_lemma(&self, lemma: &Lemma, frame: usize) -> Option<Lemma> {
        if frame == 1 {
            return None;
        }
        for c in self.frames[frame - 1].iter() {
            if c.subsume(lemma) {
                return Some(c.lemma.clone());
            }
        }
        None
    }

    pub fn _parent_lemmas(&self, lemma: &Lemma, frame: usize) -> Vec<Lemma> {
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
    pub fn similar(&self, cube: &[Lit], frame: usize) -> Vec<Cube> {
        let cube_set: HashSet<Lit> = HashSet::from_iter(cube.iter().copied());
        let mut res = HashSet::new();
        for frame in self.frames[frame..].iter() {
            for lemma in frame.iter() {
                let sec: Cube = lemma
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
    pub fn statistic(&self) {
        for f in self.frames.iter() {
            print!("{} ", f.len());
        }
        println!();
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
        unsafe { Rc::get_mut_unchecked(&mut self.frames) }
    }
}

impl IC3 {
    pub fn add_lemma(
        &mut self,
        frame: usize,
        lemma: Cube,
        contained_check: bool,
        po: Option<ProofObligation>,
    ) -> bool {
        let lemma = Lemma::new(lemma);
        if frame == 0 {
            assert!(self.frame.len() == 1);
            self.solvers[0].add_clause(&!lemma.cube());
            self.frame[0].push(FrameLemma::new(lemma, po, None));
            return false;
        }
        if contained_check && self.frame.trivial_contained(frame, &lemma).is_some() {
            return false;
        }
        assert!(!self.ts.cube_subsume_init(lemma.cube()));
        let mut begin = None;
        let mut inv_found = false;
        'fl: for i in (1..=frame).rev() {
            let mut j = 0;
            while j < self.frame[i].len() {
                let l = &self.frame[i][j];
                if begin.is_none() && l.subsume(&lemma) {
                    if l.eq(&lemma) {
                        self.frame[i].swap_remove(j);
                        let clause = !lemma.cube();
                        for k in i + 1..=frame {
                            self.solvers[k].add_clause(&clause);
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
        let clause = !lemma.cube();
        let begin = begin.unwrap_or(1);
        for i in begin..=frame {
            self.solvers[i].add_clause(&clause);
        }
        self.frame[frame].push(FrameLemma::new(lemma, po, None));
        self.frame.early = self.frame.early.min(begin);
        inv_found
    }
}
