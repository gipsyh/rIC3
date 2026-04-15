use crate::tracer::{PipeLemmaRecv, PipeLemmaSend};
use giputils::hash::GHashMap;
use ipc_channel::ipc::{IpcReceiverSet, IpcSelectionResult};
use logicrs::LitVec;
use std::io;

pub struct LemmaMgr {
    recv: IpcReceiverSet,
    rid_to_wid: GHashMap<u64, usize>,
    workers: Vec<LemmaWorker>,
}

struct LemmaWorker {
    #[allow(unused)]
    name: String,
    send: PipeLemmaSend,
}

impl LemmaMgr {
    pub fn new() -> Self {
        Self {
            recv: IpcReceiverSet::new().unwrap(),
            rid_to_wid: GHashMap::new(),
            workers: Vec::new(),
        }
    }

    pub fn add_worker(
        &mut self,
        worker: String,
        recv: PipeLemmaRecv,
        send: PipeLemmaSend,
    ) -> io::Result<()> {
        let recv_id = self.recv.add(recv)?;
        let worker_idx = self.workers.len();
        self.rid_to_wid.insert(recv_id, worker_idx);
        self.workers.push(LemmaWorker { name: worker, send });
        Ok(())
    }

    pub fn run(mut self) {
        while !self.rid_to_wid.is_empty() {
            match self.recv.select() {
                Ok(events) => {
                    for event in events {
                        match event {
                            IpcSelectionResult::MessageReceived(id, message) => {
                                let Some(&worker_idx) = self.rid_to_wid.get(&id) else {
                                    continue;
                                };
                                let (k, lemma): (Option<usize>, LitVec) = message.to().unwrap();
                                for (idx, other) in self.workers.iter().enumerate() {
                                    if idx == worker_idx {
                                        continue;
                                    }
                                    let _ = other.send.send((k, lemma.clone()));
                                }
                            }
                            IpcSelectionResult::ChannelClosed(id) => {
                                self.rid_to_wid.remove(&id);
                            }
                        }
                    }
                }
                Err(_) => {
                    return;
                }
            }
        }
    }
}
