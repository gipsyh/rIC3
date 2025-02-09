use super::IC3;
use crate::options::Options;
use giputils::hash::GHashSet;
use logic_form::{Lemma, Lit, LitVec};
use std::time::Instant;

#[derive(Clone, Copy, Debug, Default)]
pub struct DropVarParameter {
    pub limit: usize,
    max: usize,
    level: usize,
}

impl DropVarParameter {
    #[inline]
    pub fn new(limit: usize, max: usize, level: usize) -> Self {
        Self { limit, max, level }
    }

    fn sub_level(self) -> Self {
        Self {
            limit: self.limit,
            max: self.max,
            level: self.level - 1,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum MicType {
    NoMic,
    DropVar(DropVarParameter),
}

impl MicType {
    pub fn from_options(options: &Options) -> Self {
        let p = if options.ic3.ctg {
            DropVarParameter {
                limit: options.ic3.ctg_limit,
                max: options.ic3.ctg_max,
                level: 1,
            }
        } else {
            DropVarParameter::default()
        };
        MicType::DropVar(p)
    }
}

impl IC3 {
    fn down(
        &mut self,
        frame: usize,
        cube: &LitVec,
        keep: &GHashSet<Lit>,
        full: &LitVec,
        constraint: &[LitVec],
        cex: &mut Vec<(Lemma, Lemma)>,
    ) -> Option<LitVec> {
        let mut cube = cube.clone();
        self.statistic.num_down += 1;
        loop {
            if self.ts.cube_subsume_init(&cube) {
                return None;
            }
            let lemma = Lemma::new(cube.clone());
            if cex
                .iter()
                .any(|(s, t)| !lemma.subsume(s) && lemma.subsume(t))
            {
                return None;
            }
            self.statistic.num_down_sat += 1;
            if self.blocked_with_ordered_with_constrain(
                frame,
                &cube,
                false,
                true,
                constraint.to_vec(),
            ) {
                return Some(self.solvers[frame - 1].inductive_core());
            }
            let mut ret = false;
            let mut cube_new = LitVec::new();
            for lit in cube {
                if keep.contains(&lit) {
                    if let Some(true) = self.solvers[frame - 1].sat_value(lit) {
                        cube_new.push(lit);
                    } else {
                        ret = true;
                        break;
                    }
                } else if let Some(true) = self.solvers[frame - 1].sat_value(lit) {
                    if !self.solvers[frame - 1].flip_to_none(lit.var()) {
                        cube_new.push(lit);
                    }
                }
            }
            cube = cube_new;
            let mut s = LitVec::new();
            let mut t = LitVec::new();
            for l in full.iter() {
                if let Some(v) = self.solvers[frame - 1].sat_value(*l) {
                    if !self.solvers[frame - 1].flip_to_none(l.var()) {
                        s.push(l.not_if(!v));
                    }
                }
                let lt = self.ts.lit_next(*l);
                if let Some(v) = self.solvers[frame - 1].sat_value(lt) {
                    t.push(l.not_if(!v));
                }
            }
            cex.push((Lemma::new(s), Lemma::new(t)));
            if ret {
                return None;
            }
        }
    }

    fn ctg_down(
        &mut self,
        frame: usize,
        cube: &LitVec,
        keep: &GHashSet<Lit>,
        full: &LitVec,
        parameter: DropVarParameter,
    ) -> Option<LitVec> {
        let mut cube = cube.clone();
        self.statistic.num_down += 1;
        let mut ctg = 0;
        loop {
            if self.ts.cube_subsume_init(&cube) {
                return None;
            }
            self.statistic.num_down_sat += 1;
            if self.blocked_with_ordered(frame, &cube, false, true) {
                return Some(self.solvers[frame - 1].inductive_core());
            }
            for lit in cube.iter() {
                if keep.contains(lit) && !self.solvers[frame - 1].sat_value(*lit).is_some_and(|v| v)
                {
                    return None;
                }
            }
            let (model, _) = self.get_pred(frame, false);
            let cex_set: GHashSet<Lit> = GHashSet::from_iter(model.iter().cloned());
            for lit in cube.iter() {
                if keep.contains(lit) && !cex_set.contains(lit) {
                    return None;
                }
            }
            if ctg < parameter.max
                && frame > 1
                && !self.ts.cube_subsume_init(&model)
                && self.trivial_block(
                    frame - 1,
                    Lemma::new(model.clone()),
                    &[!full.clone()],
                    parameter.sub_level(),
                )
            {
                ctg += 1;
                continue;
            }
            ctg = 0;
            let mut cube_new = LitVec::new();
            for lit in cube {
                if cex_set.contains(&lit) {
                    cube_new.push(lit);
                } else if keep.contains(&lit) {
                    return None;
                }
            }
            cube = cube_new;
        }
    }

    fn handle_down_success(
        &mut self,
        _frame: usize,
        cube: LitVec,
        i: usize,
        mut new_cube: LitVec,
    ) -> (LitVec, usize) {
        new_cube = cube
            .iter()
            .filter(|l| new_cube.contains(l))
            .cloned()
            .collect();
        let new_i = new_cube
            .iter()
            .position(|l| !(cube[0..i]).contains(l))
            .unwrap_or(new_cube.len());
        if new_i < new_cube.len() {
            assert!(!(cube[0..=i]).contains(&new_cube[new_i]))
        }
        (new_cube, new_i)
    }

    pub fn mic_by_drop_var(
        &mut self,
        frame: usize,
        mut cube: LitVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> LitVec {
        let start = Instant::now();
        if parameter.level == 0 {
            self.solvers[frame - 1].set_domain(
                self.ts
                    .cube_next(&cube)
                    .iter()
                    .copied()
                    .chain(cube.iter().copied()),
            );
        }
        self.statistic.avg_mic_cube_len += cube.len();
        self.statistic.num_mic += 1;
        let mut cex = Vec::new();
        self.activity.sort_by_activity(&mut cube, true);
        let mut keep = GHashSet::new();
        let mut i = 0;
        while i < cube.len() {
            if keep.contains(&cube[i]) {
                i += 1;
                continue;
            }
            let mut removed_cube = cube.clone();
            removed_cube.remove(i);
            let mic = if parameter.level == 0 {
                self.down(frame, &removed_cube, &keep, &cube, constraint, &mut cex)
            } else {
                self.ctg_down(frame, &removed_cube, &keep, &cube, parameter)
            };
            if let Some(new_cube) = mic {
                self.statistic.mic_drop.success();
                (cube, i) = self.handle_down_success(frame, cube, i, new_cube);
                if parameter.level == 0 {
                    self.solvers[frame - 1].unset_domain();
                    self.solvers[frame - 1].set_domain(
                        self.ts
                            .cube_next(&cube)
                            .iter()
                            .copied()
                            .chain(cube.iter().copied()),
                    );
                }
            } else {
                self.statistic.mic_drop.fail();
                keep.insert(cube[i]);
                i += 1;
            }
        }
        if parameter.level == 0 {
            self.solvers[frame - 1].unset_domain();
        }
        self.activity.bump_cube_activity(&cube);
        self.statistic.block_mic_time += start.elapsed();
        cube
    }

    pub fn mic(
        &mut self,
        frame: usize,
        cube: LitVec,
        constraint: &[LitVec],
        mic_type: MicType,
    ) -> LitVec {
        match mic_type {
            MicType::NoMic => cube,
            MicType::DropVar(parameter) => self.mic_by_drop_var(frame, cube, constraint, parameter),
        }
    }
}
