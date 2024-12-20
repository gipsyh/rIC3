use super::Deep;
use logic_form::Cube;

fn handle_drop_success(cube: Cube, i: usize, mut new_cube: Cube) -> (Cube, usize) {
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

impl Deep {
    pub fn mic(&mut self, mut cube: Cube) -> Cube {
        let mut i = 0;
        while i < cube.len() {
            let mut cand = cube.clone();
            cand.remove(i);
            if !self.ts.cube_subsume_init(&cand)
                && self.solver.inductive(&cand, true, false).unwrap()
            {
                (cube, i) = handle_drop_success(cube, i, self.solver.inductive_core());
            } else {
                i += 1;
            }
        }
        cube
    }
}
