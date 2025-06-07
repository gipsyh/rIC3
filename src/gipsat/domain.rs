use super::DagCnfSolver;
use logic_form::{DagCnf, Var, VarAssign, VarSet};
use std::ops::{Deref, DerefMut};

pub struct Domain {
    domain: VarSet,
    pub fixed: u32,
}

impl Domain {
    pub fn new() -> Self {
        Self {
            domain: Default::default(),
            fixed: 0,
        }
    }

    pub fn reserve(&mut self, var: Var) {
        self.domain.reserve(var);
    }

    #[inline]
    pub fn reset(&mut self) {
        while self.domain.len() > self.fixed {
            let v = self.domain.set.pop().unwrap();
            self.domain.has[v] = false;
        }
    }

    pub fn enable_local(
        &mut self,
        domain: impl Iterator<Item = Var>,
        dc: &DagCnf,
        _value: &VarAssign,
    ) {
        self.reset();
        for r in domain {
            // if value.v(r.lit()).is_none() {
            self.domain.insert(r);
            // }
        }
        let mut now = self.fixed;
        while now < self.domain.len() {
            let v = self.domain[now];
            now += 1;
            for d in dc.dep[v].iter() {
                // if value.v(d.lit()).is_none() {
                self.domain.insert(*d);
                // }
            }
        }
    }

    #[inline]
    pub fn has(&self, var: Var) -> bool {
        self.domain.has(var)
    }

    #[inline]
    pub fn len(&self) -> u32 {
        self.domain.len()
    }
}

impl Deref for Domain {
    type Target = VarSet;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.domain
    }
}

impl DerefMut for Domain {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.domain
    }
}

impl DagCnfSolver {
    #[inline]
    pub fn add_domain(&mut self, var: Var, deps: bool) {
        assert!(self.highest_level() == 0);
        if !self.value.v(var.lit()).is_none() {
            return;
        }
        self.domain.reset();
        self.domain.domain.insert(var);
        if deps {
            let mut queue = self.dc.dep[var].clone();
            while let Some(d) = queue.pop() {
                if self.domain.has(d) {
                    continue;
                }
                self.domain.domain.insert(d);
                for dd in self.dc.dep[d].iter() {
                    queue.push(*dd);
                }
            }
        }
        self.domain.fixed = self.domain.len();
    }

    #[inline]
    pub fn push_to_vsids(&mut self) {
        assert!(self.highest_level() == 0);
        let mut now = 0;
        while now < self.domain.fixed {
            let d = self.domain.domain[now];
            if self.value.v(d.lit()).is_none() {
                self.vsids.push(d);
                now += 1;
            } else {
                self.domain.domain.swap(now, self.domain.fixed - 1);
                self.domain.domain.remove(self.domain.fixed - 1);
                self.domain.fixed -= 1;
            }
        }
        while now < self.domain.domain.len() {
            self.vsids.push(self.domain.domain[now]);
            now += 1;
        }
    }

    #[inline]
    pub fn prepare_vsids(&mut self) {
        if !self.prepared_vsids && !self.temporary_domain {
            self.prepared_vsids = true;
            for d in self.domain.domain.iter() {
                if self.value.v(d.lit()).is_none() {
                    self.vsids.push(*d);
                }
            }
        }
    }
}
