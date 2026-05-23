use crate::{McBlCertificate, McResult};
use giputils::TerminateCtrl;
use ipc_channel::ipc::{IpcReceiver, IpcSender};
use logicrs::LitVec;
use std::{
    process::exit,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

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

pub struct InterruptHandle {
    interrupted: Arc<AtomicBool>,
}

impl InterruptHandle {
    pub fn is_interrupted(&self) -> bool {
        self.interrupted.load(Ordering::SeqCst)
    }
}

pub fn install_interrupt_handler(ctrl: Arc<dyn TerminateCtrl>) -> InterruptHandle {
    let interrupted = Arc::new(AtomicBool::new(false));
    let handler_interrupted = interrupted.clone();
    let _ = ctrlc::set_handler(move || {
        if handler_interrupted.swap(true, Ordering::SeqCst) {
            crate::ui::restore_terminal();
            exit(130);
        }
        ctrl.terminate();
    });
    InterruptHandle { interrupted }
}

pub type StateIpcTx = IpcSender<(Option<usize>, McResult)>;

pub type StateIpcRx = IpcReceiver<(Option<usize>, McResult)>;

pub type LemmaIpcTx = IpcSender<(Option<usize>, LitVec)>;

pub type LemmaIpcRx = IpcReceiver<(Option<usize>, LitVec)>;

pub type CertIpcTx = IpcSender<McBlCertificate>;

pub type CertIpcRx = IpcReceiver<McBlCertificate>;
