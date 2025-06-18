use super::DagCnfSolver;
use bitfield_struct::bitfield;
use giputils::gvec::Gvec;
use giputils::hash::GHashMap;
use logicrs::{Lit, LitOrdVec};
use std::{
    mem::take,
    ops::{AddAssign, Index, MulAssign},
    ptr,
    slice::from_raw_parts,
};

#[bitfield(u32)]
struct Header {
    trans: bool,
    learnt: bool,
    reloced: bool,
    marked: bool,
    removed: bool,
    #[bits(27)]
    len: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
union Data {
    header: Header,
    lit: Lit,
    act: f32,
    cid: u32,
}

#[derive(Clone, Copy)]
pub struct Clause {
    data: *mut Data,
}

#[allow(unused)]
impl Clause {
    #[inline]
    pub fn len(&self) -> usize {
        unsafe { (*self.data).header.len() }
    }

    #[inline]
    pub fn is_trans(&self) -> bool {
        unsafe { (*self.data).header.trans() }
    }

    #[inline]
    pub fn is_learnt(&self) -> bool {
        unsafe { (*self.data).header.learnt() }
    }

    #[inline]
    pub fn is_removed(&self) -> bool {
        unsafe { (*self.data).header.removed() }
    }

    #[inline]
    pub fn remove(&mut self) {
        unsafe { (*self.data).header.set_removed(true) }
    }

    #[inline]
    pub fn is_marked(&self) -> bool {
        unsafe { (*self.data).header.marked() }
    }

    #[inline]
    pub fn mark(&mut self) {
        unsafe { (*self.data).header.set_marked(true) }
    }

    #[inline]
    pub fn unmark(&mut self) {
        unsafe { (*self.data).header.set_marked(false) }
    }

    #[inline]
    fn get_act(&self) -> f32 {
        debug_assert!(self.is_learnt());
        unsafe { (*self.data.add(self.len() + 1)).act }
    }

    #[inline]
    fn get_mut_act(&mut self) -> &mut f32 {
        debug_assert!(self.is_learnt());
        unsafe { &mut (*self.data.add(self.len() + 1)).act }
    }

    #[inline]
    pub fn swap(&mut self, a: usize, b: usize) {
        unsafe {
            ptr::swap(self.data.add(a + 1), self.data.add(b + 1));
        }
    }

    #[inline]
    pub fn swap_remove(&mut self, index: usize) {
        let len = self.len();
        unsafe {
            *self.data.add(1 + index) = *self.data.add(len);
            (*self.data).header.set_len(len - 1);
        };
    }

    #[inline]
    pub fn slice(&self) -> &[Lit] {
        unsafe { from_raw_parts(self.data.add(1) as *const Lit, self.len()) }
    }
}

impl Index<usize> for Clause {
    type Output = Lit;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        unsafe { &*(self.data.add(index + 1) as *const Lit) }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CRef(u32);

pub const CREF_NONE: CRef = CRef(u32::MAX);

impl Default for CRef {
    #[inline]
    fn default() -> Self {
        CREF_NONE
    }
}

impl From<usize> for CRef {
    #[inline]
    fn from(value: usize) -> Self {
        Self(value as _)
    }
}

#[derive(Clone)]
struct Allocator {
    data: Vec<Data>,
    wasted: usize,
}

impl Allocator {
    fn with_capacity(capacity: usize) -> Self {
        let capacity = capacity.max(1024 * 1024);
        let data = Vec::with_capacity(capacity);
        Self { data, wasted: 0 }
    }

    #[inline]
    fn len(&mut self) -> usize {
        self.data.len()
    }

    #[inline]
    pub fn get(&self, cref: CRef) -> Clause {
        Clause {
            data: unsafe { self.data.as_ptr().add(cref.0 as usize) as *mut Data },
        }
    }

    #[inline]
    fn alloc(&mut self, clause: &[Lit], trans: bool, learnt: bool) -> CRef {
        debug_assert!(!(trans && learnt));
        let cid = self.data.len();
        let mut additional = clause.len() + 1;
        if learnt {
            additional += 1;
        }
        self.data.reserve(additional);
        unsafe { self.data.set_len(self.data.len() + additional) };
        self.data[cid].header = Header::new()
            .with_len(clause.len())
            .with_trans(trans)
            .with_learnt(learnt);
        for (i, lit) in clause.iter().enumerate() {
            self.data[cid + 1 + i].lit = *lit;
        }
        if learnt {
            self.data[cid + clause.len() + 1].act = 0.0;
        }
        CRef::from(cid)
    }

    fn alloc_from(&mut self, from: &[Data]) -> CRef {
        let cid = self.data.len();
        self.data.reserve(from.len());
        self.data.extend_from_slice(from);
        cid.into()
    }

    pub fn free(&mut self, cref: CRef) {
        let mut cls = self.get(cref);
        cls.remove();
        let cref = cref.0 as usize;
        let mut len = unsafe { self.data[cref].header.len() } + 1;
        if unsafe { self.data[cref].header.learnt() } {
            len += 1;
        }
        self.wasted += len
    }

    pub fn reloc(&mut self, cid: CRef, to: &mut Allocator) -> CRef {
        let cid = cid.0 as usize;
        unsafe {
            if self.data[cid].header.reloced() {
                return CRef(self.data[cid + 1].cid);
            }
            let mut len = self.data[cid].header.len() + 1;
            if self.data[cid].header.learnt() {
                len += 1;
            }
            let rcid = to.alloc_from(&self.data[cid..cid + len]);
            self.data[cid].header.set_reloced(true);
            self.data[cid + 1].cid = rcid.0;
            rcid
        }
    }
}

impl Default for Allocator {
    fn default() -> Self {
        let data = Vec::with_capacity(1024 * 1024);
        Self { data, wasted: 0 }
    }
}

#[derive(Clone, Copy)]
pub enum ClauseKind {
    Trans,
    Lemma,
    Learnt,
    Temporary,
}

#[derive(Clone)]
pub struct ClauseDB {
    allocator: Allocator,
    pub lemmas: Gvec<CRef>,
    pub trans: Gvec<CRef>,
    pub learnt: Gvec<CRef>,
    pub temporary: Gvec<CRef>,
    act_inc: f32,
}

impl ClauseDB {
    #[inline]
    pub fn get(&self, cref: CRef) -> Clause {
        self.allocator.get(cref)
    }

    #[inline]
    pub fn alloc(&mut self, clause: &[Lit], kind: ClauseKind) -> CRef {
        let cid = self.allocator.alloc(
            clause,
            matches!(kind, ClauseKind::Trans),
            matches!(kind, ClauseKind::Learnt),
        );
        match kind {
            ClauseKind::Trans => self.trans.push(cid),
            ClauseKind::Lemma => self.lemmas.push(cid),
            ClauseKind::Learnt => self.learnt.push(cid),
            ClauseKind::Temporary => self.temporary.push(cid),
        }
        cid
    }

    #[inline]
    pub fn free(&mut self, cref: CRef) {
        self.allocator.free(cref)
    }

    #[inline]
    pub fn bump(&mut self, cref: CRef) {
        let mut cls = self.get(cref);
        if !cls.is_learnt() {
            return;
        }
        cls.get_mut_act().add_assign(self.act_inc);
        if cls.get_act() > 1e20 {
            for i in 0..self.learnt.len() {
                let l = self.learnt[i];
                let mut cls = self.get(l);
                cls.get_mut_act().mul_assign(1e-20);
            }
            self.act_inc *= 1e-20;
        }
    }

    const DECAY: f32 = 0.99;

    #[inline]
    pub fn decay(&mut self) {
        self.act_inc *= 1.0 / Self::DECAY
    }

    #[inline]
    #[allow(unused)]
    pub fn num_leanrt(&self) -> usize {
        self.learnt.len()
    }

    #[inline]
    #[allow(unused)]
    pub fn num_lemma(&self) -> usize {
        self.lemmas.len()
    }
}

impl Default for ClauseDB {
    fn default() -> Self {
        Self {
            allocator: Default::default(),
            lemmas: Default::default(),
            trans: Default::default(),
            learnt: Default::default(),
            temporary: Default::default(),
            act_inc: 1.0,
        }
    }
}

impl DagCnfSolver {
    pub fn attach_clause(&mut self, clause: &[Lit], kind: ClauseKind) -> CRef {
        debug_assert!(clause.len() > 1);
        let id = self.cdb.alloc(clause, kind);
        self.watchers.attach(id, self.cdb.get(id));
        id
    }

    pub fn detach_clause(&mut self, cref: CRef) {
        self.watchers.detach(cref, self.cdb.get(cref));
        self.cdb.free(cref);
    }

    pub fn clean_temporary(&mut self) {
        while let Some(t) = self.cdb.temporary.pop() {
            self.detach_clause(t);
        }
        if !self.value.v(self.constrain_act.lit()).is_none() {
            self.trail.retain(|l| l.var() != self.constrain_act);
            self.value.set_none(self.constrain_act);
        }
    }

    #[inline]
    pub fn locked(&self, cref: CRef) -> bool {
        let cls = self.cdb.get(cref);
        self.value.v(cls[0]).is_true() && self.reason[cls[0]] == cref
    }

    pub fn clean_leanrt(&mut self, full: bool) {
        if (full && self.cdb.learnt.len() * 15 >= self.cdb.trans.len())
            || self.cdb.learnt.len() >= self.cdb.trans.len()
        {
            self.cdb.learnt.sort_unstable_by(|a, b| {
                self.cdb
                    .allocator
                    .get(*b)
                    .get_act()
                    .partial_cmp(&self.cdb.allocator.get(*a).get_act())
                    .unwrap()
            });
            let learnt = take(&mut self.cdb.learnt);
            for i in 0..learnt.len() {
                let l = learnt[i];
                let cls = self.cdb.get(l);
                if i > learnt.len() / 3 && !self.locked(l) && cls.len() > 2 {
                    self.detach_clause(l);
                } else {
                    self.cdb.learnt.push(l);
                }
            }
            self.garbage_collect();
        }
    }

    #[inline]
    pub fn strengthen_clause(&mut self, cref: CRef, lit: Lit) {
        let mut cls = self.cdb.get(cref);
        debug_assert!(cls.len() > 2);
        let pos = cls.slice().iter().position(|l| l.eq(&lit)).unwrap();
        self.watchers.detach(cref, self.cdb.get(cref));
        cls.swap_remove(pos);
        self.watchers.attach(cref, cls);
    }

    #[allow(unused)]
    pub fn simplify_lazy_removed(&mut self) {
        if self.simplify.lazy_remove.len() * 10 <= self.cdb.num_lemma() {
            return;
        }
        let mut lazy_remove_map: GHashMap<LitOrdVec, u32> = GHashMap::new();
        for mut lr in take(&mut self.simplify.lazy_remove) {
            if lr.iter().any(|l| self.value.v(*l).is_false()) {
                continue;
            }
            lr.retain(|l| !self.value.v(*l).is_true());
            let lr = LitOrdVec::new(lr);
            let entry = lazy_remove_map.entry(lr).or_default();
            *entry += 1;
        }
        let lemmas = take(&mut self.cdb.lemmas);
        self.cdb.lemmas = self.simplify_satisfied_clauses(lemmas);
        for cref in take(&mut self.cdb.lemmas) {
            let cls = self.cdb.get(cref);
            let lemma = LitOrdVec::new(!logicrs::LitVec::from(cls.slice()));
            if let Some(r) = lazy_remove_map.get_mut(&lemma) {
                *r -= 1;
                if *r == 0 {
                    lazy_remove_map.remove(&lemma);
                }
                self.detach_clause(cref);
            } else {
                self.cdb.lemmas.push(cref);
            }
        }
    }

    pub fn garbage_collect(&mut self) {
        if self.cdb.allocator.wasted * 3 > self.cdb.allocator.len() {
            let mut to =
                Allocator::with_capacity(self.cdb.allocator.len() - self.cdb.allocator.wasted);

            for ws in self.watchers.wtrs.iter_mut() {
                for w in ws.iter_mut() {
                    w.clause = self.cdb.allocator.reloc(w.clause, &mut to);
                }
            }

            let cls = self
                .cdb
                .trans
                .iter_mut()
                .chain(self.cdb.lemmas.iter_mut())
                .chain(self.cdb.learnt.iter_mut())
                .chain(self.cdb.temporary.iter_mut());

            for c in cls {
                *c = self.cdb.allocator.reloc(*c, &mut to)
            }

            for l in self.trail.iter() {
                if self.reason[*l] != CREF_NONE {
                    self.reason[*l] = self.cdb.allocator.reloc(self.reason[*l], &mut to)
                }
            }

            self.cdb.allocator = to;
        }
    }

    #[allow(unused)]
    pub fn verify(&self, assump: &[Lit]) -> bool {
        for l in assump.iter() {
            if !self.value.v(*l).is_true() {
                return false;
            }
        }
        for cls in self
            .cdb
            .lemmas
            .iter()
            .chain(self.cdb.trans.iter())
            .chain(self.cdb.learnt.iter())
            .chain(self.cdb.temporary.iter())
        {
            let cls = self.cdb.get(*cls);
            if !cls
                .slice()
                .iter()
                .any(|l| self.value.v(*l).is_true() || !self.domain.has(l.var()))
            {
                return false;
            }
        }
        true
    }
}
