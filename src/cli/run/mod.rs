mod tui;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use crate::cli::run::tui::RunTask;
use anyhow::Ok;
use btor::Btor;
use giputils::{file::recreate_dir, hash::GHashMap};
use logicrs::fol::Term;
use rIC3::{
    McResult,
    config::EngineConfig,
    frontend::{Frontend, btor::BtorFrontend},
    wltransys::WlTransys,
};
use ratatui::widgets::TableState;
use serde::{Deserialize, Serialize};
use std::fs;
use strum::AsRefStr;

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PropMcInfo {
    id: usize,
    name: String,
    res: McResult,
    config: Option<EngineConfig>,
}

#[derive(Debug, Clone, Copy, PartialEq, AsRefStr)]
pub enum McStatus {
    Solving,
    Pause,
    Wait,
}

#[derive(Debug)]
struct PropMcState {
    prop: PropMcInfo,
    state: McStatus,
}

impl PropMcState {
    fn defalut_from_wts(wts: &WlTransys, symbols: &GHashMap<Term, String>) -> Vec<Self> {
        let mut mc = Vec::new();
        for (id, b) in wts.bad.iter().enumerate() {
            mc.push(PropMcState {
                prop: PropMcInfo {
                    id,
                    name: symbols.get(b).cloned().unwrap_or("anonymous".to_string()),
                    res: McResult::default(),
                    config: Default::default(),
                },
                state: McStatus::Wait,
            });
        }
        mc
    }
}

struct Run {
    table: TableState,
    ric3_proj: Ric3Proj,
    wts: WlTransys,
    mc: Vec<PropMcState>,
    solving: Option<RunTask>,
    should_quit: bool,
}

impl Run {
    fn new(wts: WlTransys, mc: Vec<PropMcState>, ric3_proj: Ric3Proj) -> anyhow::Result<Self> {
        fs::create_dir_all(ric3_proj.path("res"))?;
        recreate_dir(ric3_proj.path("tmp"))?;
        let mut table = TableState::default();
        table.select(Some(0));
        Ok(Self {
            table,
            ric3_proj,
            mc,
            wts,
            solving: None,
            should_quit: false,
        })
    }
}

pub fn run() -> anyhow::Result<()> {
    let ric3_cfg = Ric3Config::from_file("ric3.toml")?;
    let mut ric3_proj = Ric3Proj::new()?;
    let cached = ric3_proj.check_cached_dut(&ric3_cfg.dut.src())?;
    if cached.is_none_or(|c| !c) {
        ric3_proj.clear()?;
        Yosys::generate_btor(&ric3_cfg, ric3_proj.path("dut"))?;
        ric3_proj.cache_dut(&ric3_cfg.dut.src())?;
    }
    let btor = Btor::from_file(ric3_proj.path("dut/dut.btor"));
    let mut btorfe = BtorFrontend::new(btor);
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
        .unwrap_or(PropMcState::defalut_from_wts(&wts, &symbol));
    let mut run = Run::new(wts, mc, ric3_proj)?;
    run.run()?;
    let res: Vec<_> = run.mc.iter().map(|l| l.prop.clone()).collect();
    run.ric3_proj.cache_res(res)?;
    Ok(())
}
