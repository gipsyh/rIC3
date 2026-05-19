use crate::{config::WorkerConfigs, ic3::IC3Config};

pub struct Scheduler {
    pub num_props: usize,
    pub resolved: Vec<bool>,
    config_counter: Vec<usize>,
    configs: WorkerConfigs,
}

impl Scheduler {
    pub fn new(num_props: usize, configs: WorkerConfigs) -> Self {
        Self {
            num_props,
            resolved: vec![false; num_props],
            config_counter: vec![0; num_props],
            configs,
        }
    }

    pub fn pick(&mut self) -> Option<(usize, IC3Config)> {
        let mut best = None;
        let mut min_preset = self.configs.len();
        for p in 0..self.num_props {
            if !self.resolved[p] && self.config_counter[p] < min_preset {
                min_preset = self.config_counter[p];
                best = Some(p);
            }
        }
        let prop = best?;
        let idx = self.config_counter[prop];
        self.config_counter[prop] += 1;
        let num_configs = self.configs.len();
        assert!(num_configs > 0, "polynexus worker configs cannot be empty");
        let (name, cfg) = self.configs.iter(true).nth(idx).unwrap();
        let mut cfg = cfg
            .into_ic3()
            .unwrap_or_else(|_| panic!("polynexus worker config `{name}` is not ic3"));
        cfg.prop = Some(prop);
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
