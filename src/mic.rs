use super::IC3;
use logic_form::{Clause, Cube, Lemma, Lit, Var};
use std::{collections::HashSet, mem::swap, time::Instant};

impl IC3 {
    fn down(
        &mut self,
        frame: usize,
        cube: &Cube,
        keep: &HashSet<Lit>,
        full: &Cube,
        constrain: &[Clause],
        cex: &mut Vec<(Lemma, Lemma)>,
    ) -> Option<Cube> {
        let mut cube = cube.clone();
        self.statistic.num_down += 1;
        loop {
            if self.ts.cube_subsume_init(&cube) {
                return None;
            }
            // let lemma = Lemma::new(cube.clone());
            // if cex
            //     .iter()
            //     .any(|(s, t)| !lemma.subsume(s) && lemma.subsume(t))
            // {
            //     return None;
            // }
            self.statistic.num_down_sat += 1;
            if self
                .blocked_with_ordered_with_constrain(
                    frame,
                    &cube,
                    false,
                    true,
                    constrain.to_vec(),
                    false,
                )
                .unwrap()
            {
                return Some(self.solvers[frame - 1].inductive_core());
            }
            return None;
            // let mut ret = false;
            // let mut cube_new = Cube::new();
            // for lit in cube {
            //     if keep.contains(&lit) {
            //         if let Some(true) = self.solvers[frame - 1].sat_value(lit) {
            //             cube_new.push(lit);
            //         } else {
            //             return None;
            //         }
            //     } else if let Some(true) = self.solvers[frame - 1].sat_value(lit) {
            //         // if !self.solvers[frame - 1].flip_to_none(lit.var()) {
            //         cube_new.push(lit);
            //         // }
            //     }
            // }
            // cube = cube_new;
            // let mut s = Cube::new();
            // let mut t = Cube::new();
            // for l in full.iter() {
            //     if let Some(v) = self.solvers[frame - 1].sat_value(*l) {
            //         if !self.solvers[frame - 1].flip_to_none(l.var()) {
            //             s.push(l.not_if(!v));
            //         }
            //     }
            //     let lt = self.ts.lit_next(*l);
            //     if let Some(v) = self.solvers[frame - 1].sat_value(lt) {
            //         t.push(l.not_if(!v));
            //     }
            // }
            // cex.push((Lemma::new(s), Lemma::new(t)));
            // if ret {
            //     return None;
            // }
        }
    }

    fn ctg_down(
        &mut self,
        frame: usize,
        cube: &Cube,
        keep: &HashSet<Lit>,
        full: &Cube,
        level: usize,
    ) -> Option<Cube> {
        let mut cube = cube.clone();
        self.statistic.num_down += 1;
        let mut ctg = 0;
        loop {
            if self.ts.cube_subsume_init(&cube) {
                return None;
            }
            self.statistic.num_down_sat += 1;
            if self
                .blocked_with_ordered(frame, &cube, false, true, false)
                .unwrap()
            {
                return Some(self.solvers[frame - 1].inductive_core());
            }
            for lit in cube.iter() {
                if keep.contains(lit) && !self.solvers[frame - 1].sat_value(*lit).is_some_and(|v| v)
                {
                    return None;
                }
            }
            let (model, _) = self.get_predecessor(frame, true);
            let cex_set: HashSet<Lit> = HashSet::from_iter(model.iter().cloned());
            for lit in cube.iter() {
                if keep.contains(lit) && !cex_set.contains(lit) {
                    return None;
                }
            }
            if ctg < self.options.ic3.ctg_max && frame > 1 && !self.ts.cube_subsume_init(&model) {
                let mut limit = self.options.ic3.ctg_limit;
                if self.trivial_block(
                    frame - 1,
                    Lemma::new(model.clone()),
                    &[!full.clone()],
                    &mut limit,
                    level - 1,
                ) {
                    ctg += 1;
                    continue;
                }
            }
            ctg = 0;
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

    fn handle_down_success(&mut self, cube: Cube, i: usize, mut new_cube: Cube) -> (Cube, usize) {
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

    pub fn mic(
        &mut self,
        frame: usize,
        mut cube: Cube,
        level: usize,
        constrain: &[Clause],
    ) -> Cube {
        let start = Instant::now();
        // if level == 0 {
        //     self.solvers[frame - 1].set_domain(
        //         self.ts
        //             .cube_next(&cube)
        //             .iter()
        //             .copied()
        //             .chain(cube.iter().copied()),
        //     );
        // }
        self.statistic.avg_mic_cube_len += cube.len();
        self.statistic.num_mic += 1;
        let mut cex = Vec::new();
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
            let mic = if level > 0 {
                self.ctg_down(frame, &removed_cube, &keep, &cube, level)
            } else {
                self.down(frame, &removed_cube, &keep, &cube, constrain, &mut cex)
            };
            if let Some(new_cube) = mic {
                self.statistic.mic_drop.success();
                (cube, i) = self.handle_down_success(cube, i, new_cube);
                // if level == 0 {
                //     self.solvers[frame - 1].unset_domain();
                //     self.solvers[frame - 1].set_domain(
                //         self.ts
                //             .cube_next(&cube)
                //             .iter()
                //             .copied()
                //             .chain(cube.iter().copied()),
                //     );
                // }
            } else {
                self.statistic.mic_drop.fail();
                keep.insert(cube[i]);
                i += 1;
            }
        }
        // if level == 0 {
        //     self.solvers[frame - 1].unset_domain();
        // }
        self.activity.bump_cube_activity(&cube);
        self.statistic.block_mic_time += start.elapsed();
        cube
    }

    pub fn lazy_mic(&mut self, frame: usize, mut cube: Cube, level: usize) -> Cube {
        let start = Instant::now();
        self.statistic.avg_mic_cube_len += cube.len();
        self.statistic.num_mic += 1;
        let mut cex = Vec::new();
        let keep = HashSet::new();
        for similar in self.frame.similar(&cube, frame) {
            let mic = if level > 0 {
                self.ctg_down(frame, &similar, &keep, &cube, level)
            } else {
                self.down(frame, &similar, &keep, &cube, &[], &mut cex)
            };
            if let Some(new_cube) = mic {
                cube = new_cube;
                break;
            }
        }
        self.activity.bump_cube_activity(&cube);
        self.statistic.block_mic_time += start.elapsed();
        cube
    }

    pub fn xor_generalize(&mut self, frame: usize, mut lemma: Cube) {
        let o = lemma.len();
        for xor_round in 0..=1 {
            let mut i = 0;
            while i < lemma.len() {
                let mut j = i + 1;
                while j < lemma.len() {
                    let mut a = lemma[i];
                    let mut b = lemma[j];
                    if a.var() > b.var() {
                        swap(&mut a, &mut b);
                    }
                    if !a.polarity() {
                        a = !a;
                        b = !b;
                    }
                    if xor_round == 0 && !self.xor_var.contains_key(&(a, b)) {
                        j += 1;
                        continue;
                    }
                    let mut try_gen = lemma.clone();
                    let c = self.xor_var.get(&(a, b));
                    if let Some(c) = c {
                        assert!(i < j);
                        try_gen[i] = *c;
                        try_gen.remove(j);
                    } else {
                        try_gen[i] = !try_gen[i];
                        try_gen[j] = !try_gen[j];
                    };
                    if self.ts.cube_subsume_init(&try_gen) {
                        j += 1;
                        continue;
                    }
                    let res = self.solvers[frame - 1]
                        .inductive_with_constrain(&try_gen, true, vec![!lemma.clone()], false)
                        .unwrap();
                    self.statistic.xor_gen.statistic(res);
                    if res {
                        let core = self.solvers[frame - 1].inductive_core();
                        if c.is_some() {
                            // if core.len() < try_gen.len() {
                            //     println!("{:?} {:?}", &try_gen[i], &try_gen[j]);
                            //     println!("c {:?}", core);
                            //     println!("t {:?}", try_gen);
                            // }
                        }
                        lemma = if c.is_some() {
                            try_gen
                        } else {
                            let xor_var = self.new_var();
                            let xor_var_next = self.new_var();
                            let c = xor_var.lit();
                            self.xor_var.insert((a, b), c);
                            let trans = vec![
                                Clause::from([!a, !b, c]),
                                Clause::from([a, b, c]),
                                Clause::from([!a, b, !c]),
                                Clause::from([a, !b, !c]),
                            ];
                            let dep = vec![a.var(), b.var()];
                            self.add_latch(xor_var, xor_var_next.lit(), None, trans, dep);
                            let mut new_lemma = lemma.clone();
                            new_lemma[i] = c;
                            new_lemma.remove(j);
                            if core.len() < lemma.len() {
                                let mic = self.mic(frame, core, 0, &[]);
                                self.add_lemma(frame, mic, true, None);
                            }
                            new_lemma
                        };
                        // assert!(self.solvers[frame - 1]
                        //     .inductive(&lemma, true, false)
                        //     .unwrap());
                        continue;
                    }
                    j += 1;
                }
                i += 1;
            }
        }
        if lemma.len() < o {
            assert!(self.solvers[frame - 1]
                .inductive(&lemma, true, false)
                .unwrap());
            self.add_lemma(frame, lemma.clone(), false, None);
        }
    }

    pub fn xor_generalize2(&mut self, frame: usize, mut lemma: Cube) {
        let mut cand_lits: HashSet<Lit> = HashSet::new();
        let mut lemma_var_set: HashSet<Var> = HashSet::new();
        let mut lemma_lit_set: HashSet<Lit> = HashSet::new();
        for l in lemma.iter() {
            lemma_var_set.insert(l.var());
            lemma_lit_set.insert(*l);
        }
        for fl in self.frame[frame].iter() {
            if fl.iter().all(|l| lemma_var_set.contains(&l.var())) {
                for l in fl.iter() {
                    if lemma_lit_set.contains(&!*l) {
                        cand_lits.insert(!*l);
                    }
                }
            }
        }
        let mut not_cand_lits: HashSet<Lit> = HashSet::new();
        for l in lemma.iter() {
            if !cand_lits.contains(l) {
                not_cand_lits.insert(*l);
            }
        }

        assert!(cand_lits.len() + not_cand_lits.len() == lemma.len());

        let o = lemma.len();
        for xor_round in 0..=1 {
            let mut i = 0;
            while i < lemma.len() {
                if not_cand_lits.contains(&lemma[i]) {
                    i += 1;
                    continue;
                }
                let mut j = i + 1;
                while j < lemma.len() {
                    if not_cand_lits.contains(&lemma[j]) {
                        j += 1;
                        continue;
                    }
                    let mut a = lemma[i];
                    let mut b = lemma[j];
                    if a.var() > b.var() {
                        swap(&mut a, &mut b);
                    }
                    if !a.polarity() {
                        a = !a;
                        b = !b;
                    }
                    if xor_round == 0 && !self.xor_var.contains_key(&(a, b)) {
                        j += 1;
                        continue;
                    }
                    let mut try_gen = lemma.clone();
                    let c = self.xor_var.get(&(a, b)).cloned();
                    if let Some(c) = c {
                        assert!(i < j);
                        try_gen[i] = c;
                        try_gen.remove(j);
                    } else {
                        try_gen[i] = !try_gen[i];
                        try_gen[j] = !try_gen[j];
                    };
                    if self.ts.cube_subsume_init(&try_gen) {
                        j += 1;
                        continue;
                    }
                    let mut limit = self.options.ic3.ctg_limit;
                    let res = self.trivial_block(
                        frame,
                        Lemma::new(try_gen.clone()),
                        &[!lemma.clone()],
                        &mut limit,
                        1,
                    );
                    self.statistic.xor_gen.statistic(res);
                    if res {
                        assert!(self.solvers[frame - 1]
                            .inductive_with_constrain(&try_gen, true, vec![!lemma.clone()], false)
                            .unwrap());
                        let core = self.solvers[frame - 1].inductive_core();
                        if c.is_some() {
                            // if core.len() < try_gen.len() {
                            //     println!("{:?} {:?}", &try_gen[i], &try_gen[j]);
                            //     println!("c {:?}", core);
                            //     println!("t {:?}", try_gen);
                            // }
                        }
                        lemma = if c.is_some() {
                            try_gen
                        } else {
                            let xor_var = self.new_var();
                            let xor_var_next = self.new_var();
                            let c = xor_var.lit();
                            self.xor_var.insert((a, b), c);
                            let trans = vec![
                                Clause::from([!a, !b, c]),
                                Clause::from([a, b, c]),
                                Clause::from([!a, b, !c]),
                                Clause::from([a, !b, !c]),
                            ];
                            let dep = vec![a.var(), b.var()];
                            self.add_latch(xor_var, xor_var_next.lit(), None, trans, dep);
                            let mut new_lemma = lemma.clone();
                            new_lemma[i] = c;
                            new_lemma.remove(j);
                            if core.len() < lemma.len() {
                                let mic = self.mic(frame, core, 0, &[]);
                                self.add_lemma(frame, mic, true, None);
                            }
                            new_lemma
                        };
                        // assert!(self.solvers[frame - 1]
                        //     .inductive(&lemma, true, false)
                        //     .unwrap());
                        continue;
                    }
                    j += 1;
                }
                i += 1;
            }
        }
        if lemma.len() < o {
            assert!(self.solvers[frame - 1]
                .inductive(&lemma, true, false)
                .unwrap());
            self.add_lemma(frame, lemma.clone(), false, None);
        }
    }
}
