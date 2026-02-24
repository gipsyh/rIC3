use crate::McResult;
use log::info;
use std::{
    ops::Deref,
    sync::mpsc::{self, Receiver, Sender},
};

pub trait TracerIf: Sync + Send {
    /// Trace a result. prop is None for all properties, Some(id) for a specific property.
    fn trace_res(&mut self, _prop: Option<usize>, _res: McResult) {}
}

/// Sender part of channel tracer
pub struct ChannelTracerSx(Sender<(Option<usize>, McResult)>);

impl TracerIf for ChannelTracerSx {
    fn trace_res(&mut self, prop: Option<usize>, res: McResult) {
        let _ = self.0.send((prop, res));
    }
}

/// Receiver part of channel tracer
pub struct ChannelTracerRx(Receiver<(Option<usize>, McResult)>);

impl Deref for ChannelTracerRx {
    type Target = Receiver<(Option<usize>, McResult)>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Create a channel tracer pair (sender, receiver)
pub fn channel_tracer() -> (ChannelTracerSx, ChannelTracerRx) {
    let (tx, rx) = mpsc::channel();
    (ChannelTracerSx(tx), ChannelTracerRx(rx))
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

    pub fn trace_res(&mut self, prop: Option<usize>, res: McResult) {
        for t in self.tracers.iter_mut() {
            t.trace_res(prop, res);
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
    fn trace_res(&mut self, _prop: Option<usize>, res: McResult) {
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
