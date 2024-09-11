use crate::IC3;
use giputils::grc::Garc;
use logic_form::Cube;
use rand::{seq::SliceRandom, thread_rng};
use std::{
    mem::take,
    ops::{Deref, DerefMut},
    sync::{
        atomic::{AtomicU32, AtomicUsize, Ordering},
        Arc, RwLock,
    },
    thread::spawn,
    time::Instant,
};

#[derive(Default)]
struct PropagateShare {
    frame_idx: usize,
    task: AtomicUsize,
}

impl PropagateShare {
    fn new_task(&mut self, frame_idx: usize, num_task: usize) {
        self.frame_idx = frame_idx;
        self.task.store(num_task, Ordering::Relaxed);
    }
}

#[derive(Clone)]
enum MicTask {
    Drop(usize),
    Try(Cube),
    Random,
}

#[derive(Default)]
struct MicShare {
    frame: usize,
    cube: RwLock<Cube>,
    task: Vec<MicTask>,
    num_task: AtomicUsize,
}

impl MicShare {
    fn new_task(&mut self, frame: usize, cube: &Cube, num_worker: usize) {
        self.frame = frame;
        self.task = Vec::from_iter((0..cube.len()).map(|l| MicTask::Drop(l)).rev());
        while self.task.len() < num_worker {
            self.task.push(MicTask::Random);
        }
        *self.cube.write().unwrap() = cube.clone();
        self.num_task.store(self.task.len(), Ordering::Relaxed);
    }
}

#[derive(Default, Clone)]
pub struct Worker {
    num_worker: u32,
    wid: usize,
    task: Arc<AtomicU32>,
    propagate_share: Garc<PropagateShare>,
    mic_share: Garc<MicShare>,
    start: Arc<AtomicU32>,
    finish: Arc<AtomicU32>,
    local_propagate_res: Vec<Cube>,
}

impl IC3 {
    #[inline]
    fn worker_blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &Cube,
        ascending: bool,
        strengthen: bool,
        limit: bool,
        w: &Worker,
    ) -> Option<bool> {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.solvers[frame - 1][w.wid].inductive(&ordered_cube, strengthen, limit)
    }

    #[inline]
    fn worker_handle_task(&mut self, w: &mut Worker) {
        loop {
            if w.start.load(Ordering::Relaxed) > 0 {
                w.start.fetch_sub(1, Ordering::Release);
                break;
            }
        }
        match w.task.load(Ordering::Relaxed) {
            0 => self.worker_propagate(w),
            1 => self.worker_mic(w),
            2 => (),
            _ => panic!(),
        }
        while w.start.load(Ordering::Acquire) > 0 {}
        if w.finish
            .compare_exchange(0, w.num_worker - 1, Ordering::Release, Ordering::Relaxed)
            .is_err()
        {
            w.finish.fetch_sub(1, Ordering::Release);
        }
        while w.finish.load(Ordering::Acquire) > 0 {}
    }

    fn worker_process_task(&mut self, task: u32) {
        let num = self.options.ic3.parallelism as u32;
        let mut self_worker = self.workers[0].clone();
        self_worker.task.store(task, Ordering::Relaxed);
        self_worker.start.store(num, Ordering::Release);
        self.worker_handle_task(self_worker.deref_mut());
    }

    pub fn create_workers(&mut self) {
        if self.options.ic3.parallelism <= 1 {
            return;
        }
        let self_ptr = self as *mut Self as usize;
        self.workers.push(Garc::new(Worker::default()));
        self.workers[0].num_worker = self.options.ic3.parallelism as u32;
        for wid in 1..self.options.ic3.parallelism {
            let mut worker = Garc::new(self.workers[0].deref().clone());
            worker.wid = wid;
            self.workers.push(worker.clone());
            spawn(move || {
                let self_ptr = unsafe { &mut *(self_ptr as *mut Self) };
                loop {
                    self_ptr.worker_handle_task(&mut worker);
                }
            });
        }
    }
}

impl IC3 {
    fn worker_propagate(&mut self, w: &mut Worker) {
        w.local_propagate_res.clear();
        let frame_idx = w.propagate_share.frame_idx;
        loop {
            let task = w.propagate_share.task.load(Ordering::Relaxed);
            if task == 0 {
                return;
            }
            if w.propagate_share
                .task
                .compare_exchange(task, task - 1, Ordering::Acquire, Ordering::Relaxed)
                .is_err()
            {
                continue;
            }
            let task = task - 1;
            let lemma = self.frame[frame_idx][task].clone();
            if self
                .worker_blocked_with_ordered(frame_idx + 1, &lemma, false, false, false, w)
                .unwrap()
            {
                let core = self.solvers[frame_idx][w.wid].inductive_core();
                w.local_propagate_res.push(core);
            }
        }
    }

    pub fn parallel_propagate(&mut self) -> bool {
        for frame_idx in self.frame.early..self.level() {
            if self.options.test {
                self.frame[frame_idx].sort_by_key(|x| x.len());
                let start = Instant::now();
                for lemma in self.frame[frame_idx].iter() {
                    self.solvers[frame_idx].inductive(&lemma, false, false);
                }
                self.statistic.opro += start.elapsed();
            }
            let start = Instant::now();
            let num_task = self.frame[frame_idx].len();
            self.workers[0]
                .propagate_share
                .new_task(frame_idx, num_task);
            self.worker_process_task(0);
            self.statistic.ttime += start.elapsed();
            for mut w in self.workers.clone() {
                for core in take(&mut w.local_propagate_res) {
                    if self.add_lemma(frame_idx + 1, core, true, None) {
                        return true;
                    }
                }
            }
            self.statistic.ppro += start.elapsed();
            if self.frame[frame_idx].is_empty() {
                return true;
            }
        }
        self.frame.early = self.level();
        false
    }

    fn worker_down(&mut self, w: &mut Worker, frame: usize, cube: Cube) -> Option<Cube> {
        if self.ts.cube_subsume_init(&cube) {
            return None;
        }
        if self
            .worker_blocked_with_ordered(frame, &cube, false, true, false, w)
            .unwrap()
        {
            let core = self.solvers[frame - 1][w.wid].inductive_core();
            return Some(core);
        }
        return None;
    }

    fn worker_mic(&mut self, w: &mut Worker) {
        let frame = w.mic_share.frame;
        loop {
            let cube_lock = w.mic_share.cube.read().unwrap();
            let mut cube = cube_lock.clone();
            let mut task;
            loop {
                task = w.mic_share.num_task.load(Ordering::Relaxed);
                if task == 0 {
                    // println!("{} end", w.wid);
                    return;
                }
                if w.mic_share
                    .num_task
                    .compare_exchange_weak(task, task - 1, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
                {
                    break;
                }
            }
            drop(cube_lock);
            let cube = match &w.mic_share.task[task - 1] {
                MicTask::Drop(d) => {
                    cube.remove(*d);
                    cube
                }
                MicTask::Try(cube) => cube.clone(),
                MicTask::Random => {
                    if cube.len() <= 2 {
                        return;
                    }
                    let mut rng = thread_rng();
                    cube.shuffle(&mut rng);
                    cube.pop();
                    cube.pop();
                    cube
                }
            };
            if let Some(mic) = self.worker_down(w, frame, cube) {
                let mic_share = w.mic_share.deref_mut();
                let mut cube = mic_share.cube.write().unwrap();
                if cube.len() > mic.len() {
                    // println!("w {} succ {}", w.wid, mic.len());
                    mic_share.task = Vec::from_iter((0..mic.len()).map(|l| MicTask::Drop(l)).rev());
                    mic_share
                        .num_task
                        .store(mic_share.task.len(), Ordering::Relaxed);
                    *cube = mic;
                }
            }
        }
    }

    fn test(&mut self) {
        loop {
            let start = Instant::now();
            self.worker_process_task(2);
            dbg!(start.elapsed());
        }
    }

    pub fn parallel_mic(&mut self, frame: usize, mut cube: Cube) -> Cube {
        // self.test();
        // self.statistic.avg_mic_cube_len += cube.len();
        // println!("begin {}", cube.len());
        let mut oldmic = Default::default();
        if self.options.test {
            let start = Instant::now();
            oldmic = self.mic(frame, cube.clone(), 0, &[]);
            let time = start.elapsed();
            self.statistic.omic += time;
            // println!("old_mic {} {:?}", oldmic.len(), time);
        }
        let start = Instant::now();
        self.activity.sort_by_activity(&mut cube, true);
        self.workers[0]
            .mic_share
            .new_task(frame, &cube, self.options.ic3.parallelism);
        self.worker_process_task(1);
        let cube = self.workers[0].mic_share.cube.read().unwrap().clone();
        self.activity.bump_cube_activity(&cube);
        let time = start.elapsed();
        self.statistic.pmic += time;
        // println!("pmic end {} {:?}", cube.len(), time);
        if self.options.test {
            if oldmic.len() < cube.len() {
                self.statistic.a += 1;
            } else if oldmic.len() == cube.len() {
                self.statistic.b += 1;
            } else {
                self.statistic.c += 1;
            }
        }
        cube
    }
}
