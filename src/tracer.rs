use crate::{McResult, McWitness, transys::certify::BlWitness};
use log::info;
use logicrs::LitVec;
use std::{
    io::{self, BufRead, BufReader, PipeReader, PipeWriter, Write},
    ops::Deref,
    os::fd::{AsFd, AsRawFd},
    sync::mpsc::{self, Receiver, Sender},
};

pub trait TracerIf: Sync + Send {
    /// Trace a result. prop is None for all properties, Some(id) for a specific property.
    fn trace_state(&mut self, _prop: Option<usize>, _res: McResult) {}

    /// Trace witness
    fn trace_witness(&mut self, _w: &McWitness) {}

    /// Trace an invariant for a specific step (`Some(k)`) or for all steps (`None`).
    fn trace_invariant(&mut self, _inv: &LitVec, _k: Option<usize>) {}
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
pub struct WitnessChannelTracerSx(Sender<McWitness>);

impl TracerIf for WitnessChannelTracerSx {
    fn trace_witness(&mut self, w: &McWitness) {
        let _ = self.0.send(w.clone());
    }
}

/// Receiver part of witness channel tracer
pub struct WitnessChannelTracerRx(Receiver<McWitness>);

impl Deref for WitnessChannelTracerRx {
    type Target = Receiver<McWitness>;
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

    pub fn trace_witness(&mut self, w: &McWitness) {
        for t in self.tracers.iter_mut() {
            t.trace_witness(w);
        }
    }

    pub fn trace_invariant(&mut self, inv: &LitVec, k: Option<usize>) {
        for t in self.tracers.iter_mut() {
            t.trace_invariant(inv, k);
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

pub struct PipeTracerSend {
    state: Option<PipeWriter>,
    witness: Option<PipeWriter>,
    invariant: Option<PipeWriter>,
}

impl TracerIf for PipeTracerSend {
    fn trace_state(&mut self, prop: Option<usize>, res: McResult) {
        if let Some(state) = self.state.as_mut() {
            let line = ron::to_string(&(prop, res)).unwrap();
            let _ = writeln!(state, "{line}");
        }
    }

    fn trace_witness(&mut self, w: &McWitness) {
        if let Some(witness) = self.witness.as_mut() {
            let w = w.as_bl().unwrap();
            let line = ron::to_string(w).unwrap();
            let _ = writeln!(witness, "{line}");
        }
    }

    fn trace_invariant(&mut self, inv: &LitVec, k: Option<usize>) {
        if let Some(invariant) = self.invariant.as_mut() {
            let line = ron::to_string(&(inv, k)).unwrap();
            let _ = writeln!(invariant, "{line}");
        }
    }
}

fn pipe_has_data(reader: &BufReader<PipeReader>) -> bool {
    let fd = reader.get_ref().as_fd().as_raw_fd();
    let mut pfd = nix::libc::pollfd {
        fd,
        events: nix::libc::POLLIN,
        revents: 0,
    };
    let ret = unsafe { nix::libc::poll(&mut pfd, 1, 0) };
    assert!(
        ret >= 0,
        "failed to poll trace pipe: {}",
        io::Error::last_os_error()
    );
    ret > 0 && (pfd.revents & nix::libc::POLLIN) != 0
}

fn recv_line(reader: &mut BufReader<PipeReader>) -> String {
    let mut line = String::new();
    let len = reader.read_line(&mut line).unwrap();
    assert!(len > 0);
    line
}

fn try_recv_line(reader: &mut BufReader<PipeReader>) -> Option<String> {
    if reader.buffer().is_empty() && !pipe_has_data(reader) {
        return None;
    }
    Some(recv_line(reader))
}

pub struct PipeStateTracerRecv(BufReader<PipeReader>);

impl PipeStateTracerRecv {
    pub fn recv(&mut self) -> (Option<usize>, McResult) {
        let line = recv_line(&mut self.0);
        ron::from_str(line.trim_end()).unwrap()
    }

    pub fn pipe(&self) -> &PipeReader {
        self.0.get_ref()
    }

    pub fn try_recv(&mut self) -> Option<(Option<usize>, McResult)> {
        let line = try_recv_line(&mut self.0)?;
        Some(ron::from_str(line.trim_end()).unwrap())
    }
}

pub struct PipeWitnessTracerRecv(BufReader<PipeReader>);

impl PipeWitnessTracerRecv {
    pub fn recv(&mut self) -> McWitness {
        let line = recv_line(&mut self.0);
        let witness: BlWitness = ron::from_str(line.trim_end()).unwrap();
        McWitness::Bl(witness)
    }

    pub fn pipe(&self) -> &PipeReader {
        self.0.get_ref()
    }

    pub fn try_recv(&mut self) -> Option<McWitness> {
        let line = try_recv_line(&mut self.0)?;
        let witness: BlWitness = ron::from_str(line.trim_end()).unwrap();
        Some(McWitness::Bl(witness))
    }
}

pub struct PipeInvariantTracerRecv(BufReader<PipeReader>);

impl PipeInvariantTracerRecv {
    pub fn recv(&mut self) -> (LitVec, Option<usize>) {
        let line = recv_line(&mut self.0);
        ron::from_str(line.trim_end()).unwrap()
    }

    pub fn pipe(&self) -> &PipeReader {
        self.0.get_ref()
    }

    pub fn try_recv(&mut self) -> Option<(LitVec, Option<usize>)> {
        let line = try_recv_line(&mut self.0)?;
        Some(ron::from_str(line.trim_end()).unwrap())
    }
}

pub struct PipeTracerRecv {
    state: Option<PipeStateTracerRecv>,
    witness: Option<PipeWitnessTracerRecv>,
    invariant: Option<PipeInvariantTracerRecv>,
}

impl PipeTracerRecv {
    pub fn into_parts(
        self,
    ) -> (
        Option<PipeStateTracerRecv>,
        Option<PipeWitnessTracerRecv>,
        Option<PipeInvariantTracerRecv>,
    ) {
        (self.state, self.witness, self.invariant)
    }

    pub fn state_recv(&mut self) -> &mut PipeStateTracerRecv {
        self.state.as_mut().unwrap()
    }

    pub fn witness_recv(&mut self) -> &mut PipeWitnessTracerRecv {
        self.witness.as_mut().unwrap()
    }

    pub fn invariant_recv(&mut self) -> &mut PipeInvariantTracerRecv {
        self.invariant.as_mut().unwrap()
    }
}

pub fn pipe_tracer(
    state: bool,
    witness: bool,
    invariant: bool,
) -> (PipeTracerSend, PipeTracerRecv) {
    fn make_pipe(enabled: bool) -> (Option<PipeWriter>, Option<PipeReader>) {
        if !enabled {
            return (None, None);
        }
        let (reader, writer) = io::pipe().unwrap();
        (Some(writer), Some(reader))
    }

    let (state_tx, state_rx) = make_pipe(state);
    let (witness_tx, witness_rx) = make_pipe(witness);
    let (invariant_tx, invariant_rx) = make_pipe(invariant);

    (
        PipeTracerSend {
            state: state_tx,
            witness: witness_tx,
            invariant: invariant_tx,
        },
        PipeTracerRecv {
            state: state_rx.map(BufReader::new).map(PipeStateTracerRecv),
            witness: witness_rx.map(BufReader::new).map(PipeWitnessTracerRecv),
            invariant: invariant_rx
                .map(BufReader::new)
                .map(PipeInvariantTracerRecv),
        },
    )
}
