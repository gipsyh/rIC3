mod tui;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use anyhow::Ok;
use btor::Btor;
use giputils::file::recreate_dir;
use rIC3::{
    McResult, MpMcResult,
    config::EngineConfig,
    frontend::{Frontend, btor::BtorFrontend},
    tracer::ChannelTracerRx,
    wltransys::{WlTransys, symbol::WlTsSymbol},
};
use ratatui::widgets::TableState;
use serde::{Deserialize, Serialize};
use std::{
    fs,
    sync::{Arc, atomic::AtomicBool},
    thread::JoinHandle,
};
use strum::AsRefStr;

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PropMcInfo {
    pub id: usize,
    pub name: String,
    pub res: McResult,
    pub config: Option<EngineConfig>,
}

#[derive(Debug, Clone, Copy, PartialEq, AsRefStr)]
pub enum McStatus {
    Solving,
    Pause,
    Wait,
}

#[derive(Debug)]
pub(crate) struct PropMcState {
    pub prop: PropMcInfo,
    pub state: McStatus,
}

impl PropMcState {
    fn default_from_wts(wts: &WlTransys, symbols: &WlTsSymbol) -> Vec<Self> {
        let mut mc = Vec::new();
        for id in 0..wts.bad.len() {
            mc.push(PropMcState {
                prop: PropMcInfo {
                    id,
                    name: symbols.prop[id].clone(),
                    res: McResult::default(),
                    config: Default::default(),
                },
                state: McStatus::Wait,
            });
        }
        mc
    }
}

/// PolyNexus task handle
struct NexusTask {
    join: JoinHandle<MpMcResult>,
    state_tracer: ChannelTracerRx,
    stop: Arc<AtomicBool>,
}

pub(crate) struct Run {
    btor: Btor,
    table: TableState,
    ric3_proj: Ric3Proj,
    mc: Vec<PropMcState>,
    nexus_task: Option<NexusTask>,
    should_quit: bool,
}

impl Run {
    fn new(btor: Btor, mc: Vec<PropMcState>, ric3_proj: Ric3Proj) -> anyhow::Result<Self> {
        fs::create_dir_all(ric3_proj.path("res"))?;
        recreate_dir(ric3_proj.path("tmp"))?;
        let mut table = TableState::default();
        table.select(Some(0));
        Ok(Self {
            btor,
            table,
            ric3_proj,
            mc,
            nexus_task: None,
            should_quit: false,
        })
    }
}

pub fn run() -> anyhow::Result<()> {
    let ric3_cfg = Ric3Config::from_file("ric3.toml")?;
    let mut ric3_proj = Ric3Proj::new()?;
    let dut_hash = ric3_cfg.dut.src_hash()?;
    let cached = ric3_proj.check_cached_dut(&dut_hash)?;
    if cached.is_none_or(|c| !c) {
        ric3_proj.clear()?;
        Yosys::generate_btor(&ric3_cfg, ric3_proj.path("dut"))?;
        ric3_proj.cache_dut(&dut_hash)?;
    }
    let btor = Btor::from_file(ric3_proj.path("dut/dut.btor"));
    let mut btorfe = BtorFrontend::new(btor.clone());
    let (wts, symbol) = btorfe.wts();
    let mc = ric3_proj
        .check_cached_res()?
        .map(|p| {
            p.into_iter()
                .map(|p| PropMcState {
                    prop: p,
                    state: McStatus::Wait,
                })
                .collect()
        })
        .unwrap_or(PropMcState::default_from_wts(&wts, &symbol));
    let mut run = Run::new(btor, mc, ric3_proj)?;
    run.run()?;
    let res: Vec<_> = run.mc.iter().map(|l| l.prop.clone()).collect();
    run.ric3_proj.cache_res(res)?;
    Ok(())
}
