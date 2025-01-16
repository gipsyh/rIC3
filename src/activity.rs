use logic_form::{Cube, Lit, Var, VarMap};
use std::ops::MulAssign;
use transys::Transys;

pub struct Activity {
    activity: VarMap<f64>,
    max_act: f64,
    act_inc: f64,
}

impl Activity {
    pub fn new(ts: &Transys) -> Self {
        let mut activity = VarMap::new();
        activity.reserve(ts.max_latch);
        Self {
            activity,
            max_act: 0.0,
            act_inc: 1.0,
        }
    }

    #[inline]
    fn bump(&mut self, var: Var) {
        self.activity[var] += self.act_inc;
        self.max_act = self.max_act.max(self.activity[var]);
        if self.activity[var] > 1e100 {
            self.activity.iter_mut().for_each(|a| a.mul_assign(1e-100));
            self.act_inc *= 1e-100;
            self.max_act *= 1e-100;
        }
    }

    #[inline]
    #[allow(unused)]
    pub fn set_max_act(&mut self, var: Var) {
        self.activity[var] = self.max_act;
    }

    #[inline]
    pub fn decay(&mut self) {
        self.act_inc *= 1.0 / 0.9
    }

    pub fn bump_cube_activity(&mut self, cube: &Cube) {
        self.decay();
        cube.iter().for_each(|l| self.bump(l.var()));
    }

    pub fn sort_by_activity(&self, cube: &mut Cube, ascending: bool) {
        let ascending_func =
            |a: &Lit, b: &Lit| self.activity[*a].partial_cmp(&self.activity[*b]).unwrap();
        if ascending {
            cube.sort_by(ascending_func);
        } else {
            cube.sort_by(|a, b| ascending_func(b, a));
        }
    }

    #[allow(unused)]
    pub fn cube_average_activity(&self, cube: &Cube) -> f64 {
        let sum: f64 = cube.iter().map(|l| self.activity[*l]).sum();
        sum / cube.len() as f64
    }
}
