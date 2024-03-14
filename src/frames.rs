use crate::Ic3;
use logic_form::{Cube, Lemma, LitSet};
use std::{
    fmt::{self, Debug, Display},
    mem::take,
    ops::{Deref, DerefMut},
};

#[derive(Debug, Default)]
pub struct Frames {
    frames: Vec<Vec<Lemma>>,
    early: usize,
    lit_set: LitSet,
}

impl Frames {
    pub fn new() -> Self {
        Self {
            frames: Vec::new(),
            early: 1,
            lit_set: Default::default(),
        }
    }

    pub fn new_frame(&mut self) {
        self.frames.push(Vec::new());
    }

    pub fn early(&self) -> usize {
        self.early
    }

    pub fn reset_early(&mut self) {
        self.early = self.frames.len() - 1
    }

    pub fn statistic(&self) {
        for frame in self.frames.iter() {
            print!("{} ", frame.len());
        }
        println!();
    }
}

impl Deref for Frames {
    type Target = Vec<Vec<Lemma>>;

    fn deref(&self) -> &Self::Target {
        &self.frames
    }
}

impl DerefMut for Frames {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.frames
    }
}

impl Ic3 {
    pub fn trivial_contained(&mut self, frame: usize, lemma: &Lemma) -> bool {
        self.frames.lit_set.reserve(self.model.max_latch);
        for l in lemma.iter() {
            self.frames.lit_set.insert(*l);
        }
        for i in frame..self.frames.len() {
            for l in self.frames[i].iter() {
                if l.subsume_set(lemma, &self.frames.lit_set) {
                    self.frames.lit_set.clear();
                    return true;
                }
            }
        }
        self.frames.lit_set.clear();
        false
    }

    pub fn add_cube(&mut self, frame: usize, cube: Cube) {
        let lemma = Lemma::new(cube);
        if frame == 0 {
            assert!(self.frames.len() == 1);
            self.solvers[0].add_clause(&!lemma.cube());
            self.frames[0].push(lemma);
            return;
        }
        if self.trivial_contained(frame, &lemma) {
            return;
        }
        assert!(!self.model.cube_subsume_init(lemma.cube()));
        let mut begin = None;
        for i in (1..=frame).rev() {
            let cubes = take(&mut self.frames[i]);
            for l in cubes {
                if begin.is_none() && l.subsume(&lemma) {
                    begin = Some(i + 1);
                }
                if !lemma.subsume(&l) {
                    self.frames[i].push(l);
                }
            }
            if begin.is_some() {
                break;
            }
        }
        let clause = !lemma.cube();
        self.frames[frame].push(lemma);
        let begin = begin.unwrap_or(1);
        for i in begin..=frame {
            self.solvers[i].add_clause(&clause);
        }
        self.frames.early = self.frames.early.min(begin);
    }
}

impl Display for Frames {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for i in 1..self.frames.len() {
            f.write_fmt(format_args_nl!("frame {}", i))?;
            let frame = self.frames[i].clone();
            for c in frame.iter() {
                f.write_fmt(format_args_nl!("{:?}", c))?;
            }
        }
        Ok(())
    }
}
