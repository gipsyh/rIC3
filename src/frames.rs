use super::broadcast::PdrSolverBroadcastSender;
use crate::utils::relation::{cube_subsume, cube_subsume_init};
use logic_form::Cube;
use std::{
    fmt::Debug,
    mem::take,
    sync::{Arc, RwLock},
};

pub struct Frames {
    pub frames: RwLock<Vec<Vec<Cube>>>,
    broadcast: Vec<PdrSolverBroadcastSender>,
}

impl Frames {
    pub fn new() -> Self {
        Self {
            frames: RwLock::new(Vec::new()),
            broadcast: Vec::new(),
        }
    }

    pub fn new_frame(&mut self, broadcast: PdrSolverBroadcastSender) {
        self.frames.write().unwrap().push(Vec::new());
        if !self.broadcast.is_empty() {
            self.broadcast.last_mut().unwrap().senders.pop();
        }
        self.broadcast.push(broadcast);
    }

    pub fn add_cube(&self, frame: usize, cube: Cube) {
        assert!(cube.is_sorted_by_key(|x| x.var()));
        let mut frames = self.frames.write().unwrap();
        let begin = if frame == 0 {
            assert!(frames.len() == 1);
            0
        } else {
            if Self::trivial_contained_inner(&frames, frame, &cube) {
                return;
            }
            assert!(!cube_subsume_init(&cube));
            let mut begin = 1;
            for i in 1..=frame {
                let cubes = take(&mut frames[i]);
                for c in cubes {
                    if cube_subsume(&c, &cube) {
                        begin = i + 1;
                    }
                    if !cube_subsume(&cube, &c) {
                        frames[i].push(c);
                    }
                }
            }
            begin
        };
        frames[frame].push(cube.clone());
        drop(frames);
        let clause = Arc::new(!cube);
        for i in begin..=frame {
            self.broadcast[i].send_clause(clause.clone());
        }
    }

    fn trivial_contained_inner(frames: &[Vec<Cube>], frame: usize, cube: &Cube) -> bool {
        for i in frame..frames.len() {
            for c in frames[i].iter() {
                if cube_subsume(c, cube) {
                    return true;
                }
            }
        }
        false
    }

    pub fn trivial_contained(&self, frame: usize, cube: &Cube) -> bool {
        let frames = self.frames.read().unwrap();
        Self::trivial_contained_inner(&frames, frame, cube)
    }

    pub fn statistic(&self) {
        let frames = self.frames.read().unwrap();
        for frame in frames.iter() {
            print!("{} ", frame.len());
        }
        println!();
    }
}

impl Debug for Frames {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.frames.fmt(f)
    }
}