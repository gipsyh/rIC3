use super::IC3;
use logic_form::{Cube, Lit};
use std::collections::HashSet;

impl IC3 {
    fn ctg_down(
        &mut self,
        frame: usize,
        cube: &Cube,
        keep: &HashSet<Lit>,
        level: usize,
    ) -> Option<Cube> {
        let mut cube = cube.clone();
        self.statistic.num_down += 1;
        let mut ctgs = 0;
        loop {
            if self.ts.cube_subsume_init(&cube) {
                return None;
            }
            if self.blocked_with_ordered(frame, &cube, false, true) {
                return Some(self.solvers[frame - 1].inductive_core());
            } else {
                if level == 0 {
                    return None;
                }
                let (model, _) = self.get_pred(frame);
                if ctgs < 3 && frame > 1 && !self.ts.cube_subsume_init(&model) {
                    if self.blocked_with_ordered(frame - 1, &model, false, true) {
                        ctgs += 1;
                        let core = self.solvers[frame - 2].inductive_core();
                        let mic = self.mic(frame - 1, core, 0);
                        let (frame, mic) = self.push_lemma(frame - 1, mic);
                        self.add_lemma(frame - 1, mic, false, None);
                        continue;
                    }
                }
                ctgs = 0;
                let cex_set: HashSet<Lit> = HashSet::from_iter(model);
                let mut cube_new = Cube::new();
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
    }

    fn handle_down_success(
        &mut self,
        _frame: usize,
        cube: Cube,
        i: usize,
        mut new_cube: Cube,
    ) -> (Cube, usize) {
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

    pub fn mic(&mut self, frame: usize, mut cube: Cube, level: usize) -> Cube {
        self.statistic.avg_mic_cube_len += cube.len();
        self.statistic.num_mic += 1;
        self.activity.sort_by_activity(&mut cube, true);
        let mut keep = HashSet::new();
        let mut i = 0;
        while i < cube.len() {
            if keep.contains(&cube[i]) {
                i += 1;
                continue;
            }
            let mut removed_cube = cube.clone();
            removed_cube.remove(i);
            if let Some(new_cube) = self.ctg_down(frame, &removed_cube, &keep, level) {
                self.statistic.mic_drop.success();
                (cube, i) = self.handle_down_success(frame, cube, i, new_cube);
            } else {
                self.statistic.mic_drop.fail();
                keep.insert(cube[i]);
                i += 1;
            }
        }
        self.activity.bump_cube_activity(&cube);
        cube
    }
}
