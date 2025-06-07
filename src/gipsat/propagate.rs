use super::{
    DagCnfSolver,
    cdb::{CREF_NONE, CRef, Clause},
};
use giputils::gvec::Gvec;
use logic_form::{Lbool, Lit, LitMap, Var};

#[derive(Clone, Copy, Debug, Default)]
pub struct Watcher {
    pub clause: CRef,
    pub blocker: Lit,
}

impl Watcher {
    #[inline]
    pub fn new(clause: CRef, blocker: Lit) -> Self {
        Self { clause, blocker }
    }
}

#[derive(Default)]
pub struct Watchers {
    pub wtrs: LitMap<Gvec<Watcher>>,
}

impl Watchers {
    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.wtrs.reserve(var)
    }

    #[inline]
    pub fn attach(&mut self, cref: CRef, cls: Clause) {
        self.wtrs[!cls[0]].push(Watcher::new(cref, cls[1]));
        self.wtrs[!cls[1]].push(Watcher::new(cref, cls[0]));
    }

    #[inline]
    pub fn detach(&mut self, cref: CRef, cls: Clause) {
        for l in 0..2 {
            let l = cls[l];
            for i in (0..self.wtrs[!l].len()).rev() {
                if self.wtrs[!l][i].clause == cref {
                    self.wtrs[!l].swap_remove(i);
                    break;
                }
            }
        }
    }
}

impl DagCnfSolver {
    #[inline]
    fn propagate_full(&mut self) -> CRef {
        while self.propagated < self.trail.len() as u32 {
            let p = self.trail[self.propagated];
            self.propagated += 1;
            let mut w = 0;
            'next_cls: while w < self.watchers.wtrs[p].len() {
                let watchers = &mut self.watchers.wtrs[p];
                let blocker = watchers[w].blocker;
                if self.value.v(blocker) == Lbool::TRUE {
                    w += 1;
                    continue;
                }
                let cid = watchers[w].clause;
                let mut cref = self.cdb.get(cid);
                if cref[0] == !p {
                    cref.swap(0, 1);
                }
                debug_assert!(cref[1] == !p);
                if cref[0] != blocker && self.value.v(cref[0]) == Lbool::TRUE {
                    watchers[w].blocker = cref[0];
                    w += 1;
                    continue;
                }
                for i in 2..cref.len() {
                    let lit = cref[i];
                    if !self.value.v(lit).is_false() {
                        cref.swap(1, i);
                        watchers.swap_remove(w);
                        self.watchers.wtrs[!cref[1]].push(Watcher::new(cid, cref[0]));
                        continue 'next_cls;
                    }
                }
                watchers[w].blocker = cref[0];
                if self.value.v(cref[0]).is_false() {
                    return cid;
                }
                let assign = cref[0];
                if !self.assign_full(assign, cid) {
                    return cid;
                }
                w += 1;
            }
        }
        CREF_NONE
    }

    #[inline]
    fn propagate_domain(&mut self) -> CRef {
        while self.propagated < self.trail.len() as u32 {
            let p = self.trail[self.propagated];
            self.propagated += 1;
            let mut w = 0;
            'next_cls: while w < self.watchers.wtrs[p].len() {
                let watchers = &mut self.watchers.wtrs[p];
                let blocker = watchers[w].blocker;
                let v = self.value.v(blocker);
                if v == Lbool::TRUE || (v != Lbool::FALSE && !self.domain.has(blocker.var())) {
                    w += 1;
                    continue;
                }
                let cid = watchers[w].clause;
                let mut cref = self.cdb.get(cid);
                if cref[0] == !p {
                    cref.swap(0, 1);
                }
                debug_assert!(cref[1] == !p);
                if cref[0] != blocker {
                    let v = self.value.v(cref[0]);
                    if v == Lbool::TRUE || (v != Lbool::FALSE && !self.domain.has(cref[0].var())) {
                        watchers[w].blocker = cref[0];
                        w += 1;
                        continue;
                    }
                }
                for i in 2..cref.len() {
                    let lit = cref[i];
                    if !self.value.v(lit).is_false() {
                        cref.swap(1, i);
                        watchers.swap_remove(w);
                        self.watchers.wtrs[!cref[1]].push(Watcher::new(cid, cref[0]));
                        continue 'next_cls;
                    }
                }
                watchers[w].blocker = cref[0];
                if self.value.v(cref[0]).is_false() {
                    return cid;
                }
                let assign = cref[0];
                self.assign(assign, cid);
                w += 1;
            }
        }
        CREF_NONE
    }

    #[inline]
    pub(super) fn propagate(&mut self) -> CRef {
        if self.highest_level() == 0 {
            self.propagate_full()
        } else {
            self.propagate_domain()
        }
    }

    pub fn flip_to_none(&mut self, var: Var) -> bool {
        if self.level[var] == 0 {
            return false;
        }
        let l = var.lit();
        let l = match self.value.v(l) {
            Lbool::TRUE => l,
            Lbool::FALSE => !l,
            _ => return true,
        };
        self.value.set_none(var);
        let mut w = 0;
        'next_cls: while w < self.watchers.wtrs[!l].len() {
            let watchers = &mut self.watchers.wtrs[!l];
            let cid = watchers[w].clause;
            let mut cref = self.cdb.get(cid);
            if cref[0] == l {
                cref.swap(0, 1);
            }
            debug_assert!(cref[1] == l);
            let new_watcher = Watcher::new(cid, cref[0]);
            let v = self.value.v(cref[0]);
            if v == Lbool::TRUE || (v != Lbool::FALSE && !self.domain.has(cref[0].var())) {
                watchers[w].blocker = cref[0];
                w += 1;
                continue;
            }
            for i in 2..cref.len() {
                let lit = cref[i];
                let v = self.value.v(lit);
                if v.is_true() || (v.is_none() && !self.domain.has(lit.var())) {
                    cref.swap(1, i);
                    watchers.swap_remove(w);
                    self.watchers.wtrs[!cref[1]].push(new_watcher);
                    continue 'next_cls;
                }
            }
            self.value.set(l);
            return false;
        }
        true
    }
}
