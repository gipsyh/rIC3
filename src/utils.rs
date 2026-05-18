use crate::McResult;
use ipc_channel::ipc::{IpcReceiver, IpcSender};
use logicrs::LitVec;

pub type StateIpcTx = IpcSender<(Option<usize>, McResult)>;

pub type StateIpcRx = IpcReceiver<(Option<usize>, McResult)>;

pub type LemmaIpcTx = IpcSender<(Option<usize>, LitVec)>;

pub type LemmaIpcRx = IpcReceiver<(Option<usize>, LitVec)>;
