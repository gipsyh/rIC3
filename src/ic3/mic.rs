use super::IC3;
use crate::{options::Options, transys::TransysIf};
use giputils::hash::GHashSet;
use logic_form::{Lemma, Lit, LitVec, Var};
use satif::Satif;
use std::{cmp::Ordering, time::Instant};

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
                let lt = self.ts.next(*l);
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
                    .lits_next(&cube)
                    .iter()
                    .copied()
                    .chain(cube.iter().copied()),
            );
        }
        self.statistic.avg_mic_cube_len += cube.len();
        self.statistic.num_mic += 1;
        let mut cex = Vec::new();
        
        if self.options.ic3.topo_sort {
            if self.options.ic3.hybrid_sort {
                // Use hybrid sorting strategy
                self.sort_by_hybrid(&mut cube, frame);
            } else {
                // Sort by topological order only
                cube.sort();
                // Apply reverse if requested
                if self.options.ic3.reverse_sort {
                    cube.reverse();
                }
            }
        } else {
            // Sort by activity
            let ascending = !self.options.ic3.reverse_sort;
            self.activity.sort_by_activity(&mut cube, ascending);
        }
        
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
                            .lits_next(&cube)
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

    // Implement hybrid sorting function that considers both topological order and activity
    fn sort_by_hybrid(&mut self, cube: &mut LitVec, frame: usize) {
        // Calculate topological weight based on frame number, decreasing exponentially as frame increases
        let topo_weight = self.options.ic3.hybrid_topo_weight * 
                           (-self.options.ic3.hybrid_frame_factor * frame as f64).exp();
        let act_weight = 1.0 - topo_weight;

        // Get max and min activity values for all variables in the cube for normalization
        let mut max_activity = f64::MIN;
        let mut min_activity = f64::MAX;
        for lit in cube.iter() {
            let act = self.activity.get_activity(lit.var());
            max_activity = max_activity.max(act);
            min_activity = min_activity.min(act);
        }
        
        // Range for activity normalization
        let act_range = if max_activity > min_activity { max_activity - min_activity } else { 1.0 };
        
        // Use variable order directly for sorting, no need to get variable indices
        let vars: Vec<Var> = cube.iter().map(|lit| lit.var()).collect();
        
        // Return if vars is empty
        if vars.is_empty() {
            return;
        }
        
        // Use min and max variables as the basis for normalization
        let min_var = vars.iter().min().unwrap();
        let max_var = vars.iter().max().unwrap();

        // Create a vector containing original index, Lit, and hybrid score
        let mut indexed_cube: Vec<(usize, Lit, f64)> = cube.iter()
            .enumerate()
            .map(|(i, &lit)| {
                // Calculate normalized topological score (0-1)
                // If min_var equals max_var, all variables have the same topo score of 0.5
                let topo_score = if min_var == max_var {
                    0.5
                } else {
                    // Calculate relative position of current variable between min_var and max_var
                    // We can't directly compare variable values, but can estimate by position in sorted list
                    match vars.iter().position(|&v| v == lit.var()) {
                        Some(pos) => pos as f64 / (vars.len() - 1) as f64,
                        None => 0.5, // Default middle value
                    }
                };
                
                // Calculate normalized activity score (0-1)
                let act = self.activity.get_activity(lit.var());
                let act_score = if act_range > 0.0 { (act - min_activity) / act_range } else { 0.0 };
                
                // Calculate hybrid score
                let hybrid_score = topo_weight * topo_score + act_weight * act_score;
                
                (i, lit, hybrid_score)
            })
            .collect();
        
        // Sort by hybrid score
        if self.options.ic3.reverse_sort {
            indexed_cube.sort_by(|a, b| b.2.partial_cmp(&a.2).unwrap_or(Ordering::Equal));
        } else {
            indexed_cube.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(Ordering::Equal));
        }
        
        // Update the original cube
        *cube = indexed_cube.into_iter().map(|(_, lit, _)| lit).collect();
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
