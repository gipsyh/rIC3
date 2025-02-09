use super::{
    cdb::{CRef, CREF_NONE},
    Solver,
};
use logic_form::{Lit, LitVec, Var, VarMap};
use std::ops::{Deref, DerefMut};

#[derive(Clone, Copy, Debug, Default)]
pub enum Mark {
    #[default]
    Unseen,
    Seen,
    Removable,
    Failed,
}

#[derive(Default)]
pub struct Analyze {
    mark: VarMap<Mark>,
    clear: Vec<Lit>,
}

impl Analyze {
    pub fn reserve(&mut self, var: Var) {
        self.mark.reserve(var)
    }

    #[inline]
    pub fn seen(&mut self, lit: Lit) -> bool {
        !matches!(self.mark[lit], Mark::Unseen)
    }

    #[inline]
    pub fn see(&mut self, lit: Lit) {
        self.mark[lit] = Mark::Seen;
        self.clear.push(lit);
    }

    #[inline]
    fn mark(&mut self, lit: Lit, m: Mark) {
        self.mark[lit] = m;
        self.clear.push(lit);
    }

    fn clear(&mut self) {
        for c in self.clear.iter() {
            self.mark[*c] = Mark::Unseen;
        }
        self.clear.clear();
    }
}

impl Deref for Analyze {
    type Target = VarMap<Mark>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.mark
    }
}

impl DerefMut for Analyze {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.mark
    }
}

impl Solver {
    fn lit_redundant(&mut self, lit: Lit) -> bool {
        debug_assert!(matches!(self.analyze[lit], Mark::Unseen | Mark::Seen));
        if self.reason[lit] == CREF_NONE {
            return false;
        }
        let mut stack: Vec<(Lit, usize)> = vec![(lit, 1)];
        'a: while let Some((p, b)) = stack.pop() {
            let c = self.cdb.get(self.reason[p]);
            for i in b..c.len() {
                let l = c[i];
                if self.level[l] == 0 || matches!(self.analyze[l], Mark::Seen | Mark::Removable) {
                    continue;
                }
                if self.reason[l] == CREF_NONE || matches!(self.analyze[l], Mark::Failed) {
                    stack.push((p, 0));
                    for (l, _) in stack {
                        if let Mark::Unseen = self.analyze[l] {
                            self.analyze.mark(l, Mark::Failed);
                        }
                    }
                    return false;
                }
                stack.push((p, i + 1));
                stack.push((l, 1));
                continue 'a;
            }
            if let Mark::Unseen = self.analyze[p] {
                self.analyze.mark(p, Mark::Removable);
            }
        }
        true
    }

    fn minimal_learnt(&mut self, mut learnt: LitVec) -> LitVec {
        let mut now = 1;
        for i in 1..learnt.len() {
            if !self.lit_redundant(learnt[i]) {
                learnt[now] = learnt[i];
                now += 1
            }
        }
        learnt.truncate(now);
        learnt
    }

    pub fn analyze(&mut self, mut conflict: CRef) -> (LitVec, usize) {
        let mut learnt = LitVec::from([Lit::default()]);
        let mut path = 0;
        let mut trail_idx = self.trail.len() - 1;
        let mut resolve_lit = None;
        loop {
            self.cdb.bump(conflict);
            let cref = self.cdb.get(conflict);
            let begin = if resolve_lit.is_some() { 1 } else { 0 };
            for lit in begin..cref.len() {
                let lit = cref[lit];
                if !self.analyze.seen(lit) && self.level[lit] > 0 {
                    if lit.var() != self.constrain_act {
                        self.vsids.bump(lit.var());
                    }
                    self.analyze[lit] = Mark::Seen;
                    if self.level[lit] >= self.highest_level() as u32 {
                        path += 1;
                    } else {
                        learnt.push(lit);
                    }
                }
            }
            while !self.analyze.seen(self.trail[trail_idx]) {
                trail_idx -= 1;
            }
            self.analyze[self.trail[trail_idx]] = Mark::Unseen;
            resolve_lit = Some(self.trail[trail_idx]);
            path -= 1;
            if path == 0 {
                break;
            }
            conflict = self.reason[self.trail[trail_idx]];
        }
        learnt[0] = !resolve_lit.unwrap();
        self.analyze.clear.extend_from_slice(&learnt);
        learnt = self.minimal_learnt(learnt);
        self.analyze.clear();
        let btl = if learnt.len() == 1 {
            0
        } else {
            let max_idx = (1..learnt.len())
                .max_by_key(|idx| self.level[learnt[*idx]])
                .unwrap();
            learnt.swap(1, max_idx);
            self.level[learnt[1]]
        };
        (learnt, btl as usize)
    }

    pub fn analyze_unsat_core(&mut self, mut p: Lit) {
        self.unsat_core.clear();
        self.unsat_core.insert(p);
        if self.highest_level() == 0 {
            return;
        }
        self.analyze.see(p);
        for i in (self.pos_in_trail[0]..self.trail.len()).rev() {
            p = self.trail[i];
            if self.analyze.seen(p) {
                if self.reason[p] != CREF_NONE {
                    let c = self.cdb.get(self.reason[p]);
                    for l in 1..c.len() {
                        let l = c[l];
                        if self.level[l] > 0 {
                            self.analyze.see(l);
                        }
                    }
                } else {
                    self.unsat_core.insert(p);
                }
            }
        }
        self.analyze.clear();
    }
}
