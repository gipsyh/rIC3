use super::{cdb::CREF_NONE, Solver};
use giputils::{gvec::Gvec, OptionU32};
use logic_form::{Lbool, Lit, LitVec, Var, VarMap};
use rand::Rng;
use std::ops::{Index, MulAssign};

#[derive(Default)]
pub struct BinaryHeap {
    heap: Gvec<Var>,
    pos: VarMap<OptionU32>,
}

impl BinaryHeap {
    #[inline]
    fn reserve(&mut self, var: Var) {
        self.pos.reserve(var);
    }

    #[inline]
    pub fn clear(&mut self) {
        for v in self.heap.iter() {
            self.pos[*v] = OptionU32::NONE;
        }
        self.heap.clear();
    }

    #[inline]
    fn up(&mut self, v: Var, activity: &Activity) {
        let mut idx = match self.pos[v] {
            OptionU32::NONE => return,
            idx => *idx,
        };
        while idx != 0 {
            let pidx = (idx - 1) >> 1;
            if activity[self.heap[pidx]] >= activity[v] {
                break;
            }
            self.heap[idx] = self.heap[pidx];
            *self.pos[self.heap[idx]] = idx;
            idx = pidx;
        }
        self.heap[idx] = v;
        *self.pos[v] = idx;
    }

    #[inline]
    fn down(&mut self, mut idx: u32, activity: &Activity) {
        let v = self.heap[idx];
        loop {
            let left = (idx << 1) + 1;
            if left >= self.heap.len() {
                break;
            }
            let right = left + 1;
            let child = if right < self.heap.len()
                && activity[self.heap[right]] > activity[self.heap[left]]
            {
                right
            } else {
                left
            };
            if activity[v] >= activity[self.heap[child]] {
                break;
            }
            self.heap[idx] = self.heap[child];
            *self.pos[self.heap[idx]] = idx;
            idx = child;
        }
        self.heap[idx] = v;
        *self.pos[v] = idx;
    }

    #[inline]
    pub fn push(&mut self, var: Var, activity: &Activity) {
        if self.pos[var].is_some() {
            return;
        }
        let idx = self.heap.len();
        self.heap.push(var);
        *self.pos[var] = idx;
        self.up(var, activity);
    }

    #[inline]
    pub fn pop(&mut self, activity: &Activity) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let value = self.heap[0];
        self.heap[0] = self.heap[self.heap.len() - 1];
        *self.pos[self.heap[0]] = 0;
        self.pos[value] = OptionU32::NONE;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.down(0, activity);
        }
        Some(value)
    }
}

pub struct Activity {
    activity: VarMap<f64>,
    act_inc: f64,
    bucket_heap: BinaryHeap,
    bucket_table: Gvec<u32>,
}

impl Index<Var> for Activity {
    type Output = f64;

    #[inline]
    fn index(&self, index: Var) -> &Self::Output {
        &self.activity[index]
    }
}

impl Activity {
    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.activity.reserve(var);
        self.bucket_heap.reserve(var);
    }

    #[inline]
    fn check(&mut self, var: Var) {
        let act = unsafe { &mut *(self as *mut Activity) };
        if self.bucket_heap.pos[var].is_none() {
            self.bucket_heap.push(var, act);
            let b = 32 - (self.bucket_table.len() - 1).leading_zeros();
            *self.bucket_table.last_mut().unwrap() = b;
            self.bucket_table.push(b + 1);
        }
        assert!(self.bucket_heap.pos[var].is_some())
    }

    #[inline]
    fn bucket(&self, var: Var) -> u32 {
        match self.bucket_heap.pos[var] {
            OptionU32::NONE => self.bucket_table[self.bucket_table.len() - 1],
            b => self.bucket_table[*b],
        }
    }

    #[inline]
    pub fn bump(&mut self, var: Var) {
        self.activity[var] += self.act_inc;
        self.check(var);
        let act = unsafe { &mut *(self as *mut Activity) };
        self.bucket_heap.up(var, act);
        if self.activity[var] > 1e100 {
            self.activity.iter_mut().for_each(|a| a.mul_assign(1e-100));
            self.act_inc *= 1e-100;
        }
    }

    const DECAY: f64 = 0.95;

    #[inline]
    pub fn decay(&mut self) {
        self.act_inc *= 1.0 / Self::DECAY
    }

    #[allow(unused)]
    pub fn sort_by_activity(&self, cube: &mut LitVec, ascending: bool) {
        if ascending {
            cube.sort_by(|a, b| self.activity[*a].partial_cmp(&self.activity[*b]).unwrap());
        } else {
            cube.sort_by(|a, b| self.activity[*b].partial_cmp(&self.activity[*a]).unwrap());
        }
    }
}

impl Default for Activity {
    fn default() -> Self {
        let mut bucket_table = Gvec::new();
        bucket_table.push(0);
        Self {
            act_inc: 1.0,
            activity: Default::default(),
            bucket_heap: Default::default(),
            bucket_table,
        }
    }
}

pub struct Vsids {
    pub activity: Activity,

    pub heap: BinaryHeap,
    pub bucket: Bucket,
    pub enable_bucket: bool,
}

impl Vsids {
    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.heap.reserve(var);
        self.activity.reserve(var);
        self.bucket.reserve(var);
    }

    #[inline]
    pub fn push(&mut self, var: Var) {
        if self.enable_bucket {
            return self.bucket.push(var, &self.activity);
        }
        self.heap.push(var, &self.activity)
    }

    #[inline]
    pub fn pop(&mut self) -> Option<Var> {
        if self.enable_bucket {
            return self.bucket.pop();
        }
        self.heap.pop(&self.activity)
    }

    #[inline]
    pub fn bump(&mut self, var: Var) {
        self.activity.bump(var);
        if !self.enable_bucket {
            self.heap.up(var, &self.activity);
        }
        self.bucket
            .buckets
            .reserve(self.activity.bucket_table[self.activity.bucket_table.len() - 1] + 1);
    }

    #[inline]
    pub fn decay(&mut self) {
        self.activity.decay();
    }
}

impl Default for Vsids {
    fn default() -> Self {
        Self {
            activity: Default::default(),
            heap: Default::default(),
            bucket: Bucket::new(),
            enable_bucket: true,
        }
    }
}

pub struct Bucket {
    buckets: Gvec<Gvec<Var>>,
    in_bucket: VarMap<bool>,
    head: u32,
}

impl Bucket {
    #[inline]
    pub fn new() -> Self {
        let mut buckets: Gvec<_> = Gvec::new();
        buckets.reserve(10);
        Self {
            buckets,
            in_bucket: Default::default(),
            head: Default::default(),
        }
    }

    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.in_bucket.reserve(var);
    }

    #[inline]
    pub fn push(&mut self, var: Var, activity: &Activity) {
        if self.in_bucket[var] {
            return;
        }
        let bucket = activity.bucket(var);
        if self.head > bucket {
            self.head = bucket;
        }
        self.buckets[bucket].push(var);
        self.in_bucket[var] = true;
    }

    #[inline]
    pub fn pop(&mut self) -> Option<Var> {
        while self.head < self.buckets.len() {
            if !self.buckets[self.head].is_empty() {
                let var = self.buckets[self.head].pop().unwrap();
                self.in_bucket[var] = false;
                return Some(var);
            }
            self.head += 1;
        }
        None
    }

    #[inline]
    pub fn clear(&mut self) {
        while self.head < self.buckets.len() {
            while let Some(var) = self.buckets[self.head].pop() {
                self.in_bucket[var] = false;
            }
            self.head += 1;
        }
        for b in self.buckets.iter_mut() {
            b.clear();
        }
        self.head = 0;
    }
}

impl Solver {
    #[inline]
    pub fn decide(&mut self) -> bool {
        while let Some(decide) = self.vsids.pop() {
            if self.value.v(decide.lit()).is_none() {
                let decide = if self.phase_saving[decide].is_none() {
                    Lit::new(decide, self.rng.random_bool(0.5))
                } else {
                    Lit::new(decide, self.phase_saving[decide] != Lbool::FALSE)
                };
                self.pos_in_trail.push(self.trail.len());
                self.assign(decide, CREF_NONE);
                return true;
            }
        }
        false
    }
}
