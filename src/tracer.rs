use crate::{McBlCertificate, McResult};
use ipc_channel::{
    TryRecvError,
    ipc::{self, IpcReceiver, IpcSender},
};
use log::info;
use logicrs::LitVec;
use serde::{Serialize, de::DeserializeOwned};
use std::{
    ops::Deref,
    sync::mpsc::{self, Receiver, Sender},
};

pub trait TracerIf: Sync + Send {
    /// Trace a result. prop is None for all properties, Some(id) for a specific property.
    fn trace_state(&mut self, _prop: Option<usize>, _res: McResult) {}

    /// Trace cex
    fn trace_cert(&mut self, _c: &McBlCertificate) {}

    /// Trace a lemma for a specific step (`Some(k)`) or for all steps (`None`).
    fn trace_lemma(&mut self, _inv: &LitVec, _k: Option<usize>) {}
}

/// Sender part of state channel tracer
pub struct StateChannelTracerSx(Sender<(Option<usize>, McResult)>);

impl TracerIf for StateChannelTracerSx {
    fn trace_state(&mut self, prop: Option<usize>, res: McResult) {
        let _ = self.0.send((prop, res));
    }
}

/// Receiver part of state channel tracer
pub struct StateChannelTracerRx(Receiver<(Option<usize>, McResult)>);

impl Deref for StateChannelTracerRx {
    type Target = Receiver<(Option<usize>, McResult)>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Create a state channel tracer pair (sender, receiver)
pub fn state_channel_tracer() -> (StateChannelTracerSx, StateChannelTracerRx) {
    let (tx, rx) = mpsc::channel();
    (StateChannelTracerSx(tx), StateChannelTracerRx(rx))
}

/// Sender part of witness channel tracer
pub struct WitnessChannelTracerSx(Sender<McBlCertificate>);

impl TracerIf for WitnessChannelTracerSx {
    fn trace_cert(&mut self, c: &McBlCertificate) {
        let _ = self.0.send(c.clone());
    }
}

/// Receiver part of witness channel tracer
pub struct WitnessChannelTracerRx(Receiver<McBlCertificate>);

impl Deref for WitnessChannelTracerRx {
    type Target = Receiver<McBlCertificate>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Create a witness channel tracer pair (sender, receiver)
pub fn witness_channel_tracer() -> (WitnessChannelTracerSx, WitnessChannelTracerRx) {
    let (tx, rx) = mpsc::channel();
    (WitnessChannelTracerSx(tx), WitnessChannelTracerRx(rx))
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

    pub fn trace_state(&mut self, prop: Option<usize>, res: McResult) {
        for t in self.tracers.iter_mut() {
            t.trace_state(prop, res);
        }
    }

    pub fn trace_cert(&mut self, c: &McBlCertificate) {
        for t in self.tracers.iter_mut() {
            t.trace_cert(c);
        }
    }

    pub fn trace_lemma(&mut self, inv: &LitVec, k: Option<usize>) {
        for t in self.tracers.iter_mut() {
            t.trace_lemma(inv, k);
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
    fn trace_state(&mut self, _prop: Option<usize>, res: McResult) {
        match res {
            McResult::UNSAT => info!("{} proved the property", self.name),
            McResult::SAT(d) => info!("{} found a counterexample at depth {d}", self.name),
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

pub struct PipeTracerSend {
    state: Option<IpcSender<(Option<usize>, McResult)>>,
    cert: Option<IpcSender<McBlCertificate>>,
    lemma: Option<IpcSender<(Option<usize>, LitVec)>>,
}

impl TracerIf for PipeTracerSend {
    fn trace_state(&mut self, prop: Option<usize>, res: McResult) {
        if let Some(state) = self.state.as_mut() {
            let _ = state.send((prop, res));
        }
    }

    fn trace_cert(&mut self, c: &McBlCertificate) {
        if let Some(cert) = self.cert.as_mut() {
            let _ = cert.send(c.clone());
        }
    }

    fn trace_lemma(&mut self, l: &LitVec, k: Option<usize>) {
        if let Some(lemma) = self.lemma.as_mut() {
            let _ = lemma.send((k, l.clone()));
        }
    }
}

pub type PipeStateRecv = IpcReceiver<(Option<usize>, McResult)>;
pub type PipeCertRecv = IpcReceiver<McBlCertificate>;
pub type PipeLemmaSend = IpcSender<(Option<usize>, LitVec)>;
pub type PipeLemmaRecv = IpcReceiver<(Option<usize>, LitVec)>;

pub struct PipeTracerRecv {
    state: Option<PipeStateRecv>,
    cert: Option<PipeCertRecv>,
    lemma: Option<PipeLemmaRecv>,
}

impl PipeTracerRecv {
    pub fn into_parts(
        self,
    ) -> (
        Option<PipeStateRecv>,
        Option<PipeCertRecv>,
        Option<PipeLemmaRecv>,
    ) {
        (self.state, self.cert, self.lemma)
    }
}

pub fn pipe_tracer(state: bool, cert: bool, lemma: bool) -> (PipeTracerSend, PipeTracerRecv) {
    fn make_channel<T: DeserializeOwned + Serialize>(
        enabled: bool,
    ) -> (Option<IpcSender<T>>, Option<IpcReceiver<T>>) {
        if !enabled {
            return (None, None);
        }
        let (sender, receiver) = ipc::channel().unwrap();
        (Some(sender), Some(receiver))
    }

    let (state_tx, state_rx) = make_channel(state);
    let (cert_tx, cert_rx) = make_channel(cert);
    let (lemma_tx, lemma_rx) = make_channel(lemma);

    (
        PipeTracerSend {
            state: state_tx,
            cert: cert_tx,
            lemma: lemma_tx,
        },
        PipeTracerRecv {
            state: state_rx,
            cert: cert_rx,
            lemma: lemma_rx,
        },
    )
}

pub trait ExtractorIf: Send {
    fn extract_lemma(&mut self) -> Option<(Option<usize>, LitVec)>;
}

impl ExtractorIf for PipeLemmaRecv {
    fn extract_lemma(&mut self) -> Option<(Option<usize>, LitVec)> {
        match self.try_recv() {
            Ok(r) => Some(r),
            Err(TryRecvError::Empty) => None,
            _ => panic!(),
        }
    }
}
