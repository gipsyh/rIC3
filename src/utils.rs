use crate::{McBlCertificate, McResult};
use giputils::TerminateCtrl;
use ipc_channel::ipc::{IpcReceiver, IpcSender};
use logicrs::LitVec;
use std::sync::atomic::{AtomicBool, Ordering};

/// External control handle for engines.
#[derive(Debug)]
pub struct EngineCtrl {
    terminate: AtomicBool,
}

impl Default for EngineCtrl {
    fn default() -> Self {
        Self {
            terminate: AtomicBool::new(false),
        }
    }
}

impl EngineCtrl {
    pub fn new() -> Self {
        Self::default()
    }
}

impl TerminateCtrl for EngineCtrl {
    fn terminate(&self) {
        self.terminate.store(true, Ordering::SeqCst);
    }

    fn is_terminated(&self) -> bool {
        self.terminate.load(Ordering::SeqCst)
    }
}

pub type StateIpcTx = IpcSender<(Option<usize>, McResult)>;

pub type StateIpcRx = IpcReceiver<(Option<usize>, McResult)>;

pub type LemmaIpcTx = IpcSender<(Option<usize>, LitVec)>;

pub type LemmaIpcRx = IpcReceiver<(Option<usize>, LitVec)>;

pub type CertIpcTx = IpcSender<McBlCertificate>;

pub type CertIpcRx = IpcReceiver<McBlCertificate>;
