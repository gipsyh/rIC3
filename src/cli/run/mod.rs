mod tui;

use crate::cli::{cache::Ric3Proj, yosys::Yosys};
use btor::Btor;
use giputils::hash::GHashMap;
use logicrs::fol::Term;
use rIC3::{
    McResult,
    config::EngineConfig,
    frontend::{Frontend, btor::BtorFrontend},
    wltransys::WlTransys,
};
use ratatui::widgets::TableState;
use serde::{Deserialize, Serialize};
use std::{
    fs,
    path::{Path, PathBuf},
};

#[derive(Deserialize, Debug)]
pub struct Ric3Config {
    pub dut: Dut,
}

impl Ric3Config {
    pub fn from_file<P: AsRef<Path>>(p: P) -> anyhow::Result<Self> {
        let config_content = fs::read_to_string(p)?;
        let config: Self = toml::from_str(&config_content)?;
        Ok(config)
    }

    pub fn dut_src(&self) -> Vec<PathBuf> {
        self.dut.files.clone()
    }
}

#[derive(Deserialize, Debug)]
pub struct Dut {
    pub top: String,
    pub files: Vec<PathBuf>,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PropMcInfo {
    id: usize,
    name: String,
    res: McResult,
    config: Option<EngineConfig>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum McStatus {
    Solving,
    Pause,
}

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
                state: McStatus::Pause,
            });
        }
        mc
    }
}

struct Run {
    table: TableState,
    should_quit: bool,
    mc: Vec<PropMcState>,
}

impl Run {
    fn new(mc: Vec<PropMcState>) -> Self {
        let mut table = TableState::default();
        table.select(Some(0));
        Self {
            table,
            should_quit: false,
            mc,
        }
    }
}

pub fn run() -> anyhow::Result<()> {
    let ric3_cfg = Ric3Config::from_file("ric3.toml")?;
    let ric3_proj = Ric3Proj::new()?;
    let same = ric3_proj.check_cached_src(&ric3_cfg.dut_src())?;
    if !same {
        ric3_proj.clear()?;
        Yosys::generate_btor(&ric3_cfg, &ric3_proj);
        ric3_proj.cache_src(&ric3_cfg.dut_src())?;
    }

    let btor = Btor::from_file(ric3_proj.dut_path().join("dut.btor"));
    let mut btorfe = BtorFrontend::new(btor);
    let (wts, symbol) = btorfe.wts();
    let mc = ric3_proj
        .check_cached_res()?
        .map(|p| {
            p.into_iter()
                .map(|p| PropMcState {
                    prop: p,
                    state: McStatus::Pause,
                })
                .collect()
        })
        .unwrap_or(PropMcState::defalut_from_wts(&wts, &symbol));

    // let res = if let Some(r) = res.get(&0) {
    //     r.clone()
    // } else {
    //     let engine_cfg = EngineConfig::parse_from(["", "-e", "portfolio"]);
    //     let cert_file = ric3_proj.res_path().join("cert");
    //     let mut engine = Portfolio::new(btor_file, Some(cert_file), engine_cfg);
    //     let res = engine.check();
    //     let mut map = HashMap::new();
    //     match res {
    //         Some(res) => {
    //             let r = if res {
    //                 McResult::Safe
    //             } else {
    //                 McResult::Unsafe(0)
    //             };
    //             map.insert(0, r);
    //             ric3_proj.cache_res(map)?;
    //             r
    //         }
    //         None => todo!(),
    //     }
    // };
    let mut run = Run::new(mc);
    run.run()
}
