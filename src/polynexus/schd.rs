use crate::ic3::IC3Config;

pub struct Scheduler {
    pub num_props: usize,
    pub resolved: Vec<bool>,
    config_counter: Vec<usize>,
    configs: Vec<IC3Config>,
}

impl Scheduler {
    pub fn new(num_props: usize, configs: Vec<IC3Config>) -> Self {
        Self {
            num_props,
            resolved: vec![false; num_props],
            config_counter: vec![0; num_props],
            configs,
        }
    }

    pub fn pick(&mut self) -> Option<(usize, IC3Config)> {
        let mut best = None;
        let mut min_preset = usize::MAX;
        for p in 0..self.num_props {
            if !self.resolved[p] && self.config_counter[p] < min_preset {
                min_preset = self.config_counter[p];
                best = Some(p);
            }
        }
        let prop = best?;
        let idx = self.config_counter[prop];
        self.config_counter[prop] += 1;
        let preset_idx = idx % self.configs.len();
        let mut cfg = self.configs[preset_idx].clone();
        cfg.prop = Some(prop);
        cfg.base.rseed = cfg.base.rseed.wrapping_add(idx as u64);
        Some((prop, cfg))
    }

    pub fn resolve(&mut self, prop: usize) {
        if !self.resolved[prop] {
            self.resolved[prop] = true;
        }
    }

    pub fn all_resolved(&self) -> bool {
        self.resolved.iter().all(|x| *x)
    }
}
