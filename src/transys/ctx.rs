use super::{Transys, TransysIf};
use logicrs::{DagCnf, Lit, LitMap, LitVec, LitVvec, Var, VarMap};

#[derive(Clone, Debug)]
pub struct TransysCtx {
    pub input: Vec<Var>,
    pub latch: Vec<Var>,
    pub init: LitVvec,
    pub init_map: VarMap<Option<Lit>>,
    pub bad: LitVec,
    pub constraint: LitVec,
    pub rel: DagCnf,
    is_latch: VarMap<bool>,
    next_map: LitMap<Lit>,
    pub max_latch: Var,
}

impl TransysIf for TransysCtx {
    #[inline]
    fn max_var(&self) -> Var {
        self.rel.max_var()
    }

    #[inline]
    fn new_var(&mut self) -> Var {
        let max_var = self.rel.new_var();
        self.init_map.reserve(max_var);
        self.next_map.reserve(max_var);
        self.is_latch.reserve(max_var);
        max_var
    }

    #[inline]
    fn input(&self) -> impl Iterator<Item = Var> {
        self.input.iter().copied()
    }

    #[inline]
    fn latch(&self) -> impl Iterator<Item = Var> {
        self.latch.iter().copied()
    }

    #[inline]
    fn is_latch(&self, var: Var) -> bool {
        self.is_latch[var]
    }

    #[inline]
    fn init(&self, latch: Var) -> Option<Lit> {
        self.init_map[latch]
    }

    #[inline]
    fn next(&self, lit: Lit) -> Lit {
        self.next_map[lit]
    }

    #[inline]
    fn constraint(&self) -> impl Iterator<Item = Lit> {
        self.constraint.iter().copied()
    }

    #[inline]
    fn trans(&self) -> impl Iterator<Item = &LitVec> {
        self.rel.clause()
    }

    fn add_init(&mut self, latch: Var, init: Lit) {
        self.init_map[latch] = Some(init);
        if let Some(i) = init.try_constant() {
            self.init.push(LitVec::from([Lit::new(latch, i)]));
        } else {
            self.init.push(LitVec::from([latch.lit(), !init]));
            self.init.push(LitVec::from([!latch.lit(), init]));
        }
    }
}

impl TransysCtx {
    #[inline]
    pub fn num_var(&self) -> usize {
        Into::<usize>::into(self.max_var()) + 1
    }

    #[inline]
    pub fn cube_subsume_init(&self, x: &[Lit]) -> bool {
        for x in x {
            if let Some(init) = self.init_map[x.var()]
                && let Some(i) = init.try_constant()
                && i != x.polarity()
            {
                return false;
            }
        }
        true
    }
}

impl Transys {
    pub fn ctx(&self) -> TransysCtx {
        let input = self.input.clone();
        let mut latch = self.latch.clone();
        latch.sort();
        let max_var = self.rel.max_var();
        let max_latch = *latch.iter().max().unwrap_or(&Var::CONST);
        let mut is_latch = VarMap::new_with(max_var);
        let mut init = LitVvec::new();
        let mut init_map = VarMap::new_with(max_latch);
        let mut next_map = LitMap::new_with(max_latch);
        for &v in latch.iter() {
            let l = v.lit();
            is_latch[v] = true;
            let n = self.next(l);
            next_map[l] = n;
            next_map[!l] = !n;
            if let Some(i) = self.init.get(&v).copied() {
                init_map[v] = Some(i);
                if let Some(i) = i.try_constant() {
                    init.push(LitVec::from([Lit::new(v, i)]));
                } else {
                    init.push(LitVec::from([l, !i]));
                    init.push(LitVec::from([!l, i]));
                }
            }
        }
        TransysCtx {
            input,
            latch,
            init,
            init_map,
            bad: self.bad.clone(),
            constraint: self.constraint.clone(),
            rel: self.rel.clone(),
            is_latch,
            next_map,
            max_latch,
        }
    }
}
