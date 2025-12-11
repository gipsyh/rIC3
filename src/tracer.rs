use crate::McResult;
use log::info;

pub trait TracerIf {
    fn trace_res(&mut self, _res: McResult) {}
}

#[derive(Default)]
pub struct Tracer {
    tracers: Vec<Box<dyn TracerIf>>,
}

impl Tracer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracers.push(tracer);
    }

    pub fn trace_res(&mut self, res: McResult) {
        for t in self.tracers.iter_mut() {
            t.trace_res(res);
        }
    }
}

pub struct LogTracer {
    name: String,
    unknown: Option<usize>,
}

impl LogTracer {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            unknown: None,
        }
    }

    pub fn update_unknow(&mut self, d: usize) -> bool {
        match self.unknown {
            None if d == 0 => {
                self.unknown = Some(d);
                true
            }
            Some(l) if d == l + 1 => {
                self.unknown = Some(d);
                true
            }
            _ => false,
        }
    }
}

impl TracerIf for LogTracer {
    fn trace_res(&mut self, res: McResult) {
        match res {
            McResult::Safe => info!("{} proved the property", self.name),
            McResult::Unsafe(d) => info!("{} found a counterexample at depth {d}", self.name),
            McResult::Unknown(Some(d)) => {
                if self.update_unknow(d) {
                    info!("{} found no counterexample up to depth {d}", self.name)
                } else {
                    info!("{} found no counterexample at exact depth {d}", self.name)
                }
            }
            _ => (),
        }
    }
}
