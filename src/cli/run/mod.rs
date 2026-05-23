mod ui;

use super::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use btor::Btor;
use clap::{Args, ValueEnum};
use giputils::file::recreate_dir;
use rIC3::{
    Engine, McBlCertificate, McResult, MpEngine, MpMcResult,
    config::EngineConfig,
    frontend::{Frontend, btor::BtorFrontend},
    polynexus::{PolyNexus, PolyNexusConfig},
    tracer::{
        StateChannelTracerRx, WitnessChannelTracerRx, state_channel_tracer, witness_channel_tracer,
    },
    utils::{InterruptHandle, install_interrupt_handler},
    wltransys::{WlTransys, symbol::WlTsSymbol},
};
use serde::{Deserialize, Serialize};
use std::{
    fs::{self, File},
    io::{BufWriter, IsTerminal},
    num::NonZeroUsize,
    thread::{JoinHandle, spawn},
    time::{Duration, Instant},
};
use strum::AsRefStr;

#[derive(Args, Debug, Clone, Default)]
pub struct RunConfig {
    /// Number of worker processes (auto-detect if omitted)
    #[arg(long = "workers")]
    pub workers: Option<NonZeroUsize>,

    /// Run display mode
    #[arg(long = "ui", value_enum, default_value_t = RunUi::Auto)]
    pub ui: RunUi,
}

#[derive(ValueEnum, Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum RunUi {
    /// Pick a terminal-friendly display automatically
    #[default]
    Auto,
    /// Docker-pull style live progress lines
    Tui,
    /// Print one line per status update
    Plain,
}

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
    pub start_time: Option<Instant>,
    pub time: Duration,
}

impl PropMcState {
    pub(crate) fn default_from_wts(wts: &WlTransys, symbols: &WlTsSymbol) -> Vec<Self> {
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
                start_time: None,
                time: Duration::ZERO,
            });
        }
        mc
    }
}

/// PolyNexus task handle
pub(crate) struct NexusTask {
    join: JoinHandle<(MpMcResult, PolyNexus)>,
    state_trx: StateChannelTracerRx,
    wit_trx: WitnessChannelTracerRx,
    #[allow(unused)]
    ctrl: InterruptHandle,
}

pub(crate) struct Run {
    #[allow(unused)]
    btor: Btor,
    btorfe: BtorFrontend,
    wsym: WlTsSymbol,
    ric3_proj: Ric3Proj,
    mc: Vec<PropMcState>,
    nexus_task: Option<NexusTask>,
    cfg: RunConfig,
}

#[derive(Debug, Default)]
pub(crate) struct RunUpdates {
    pub state: Vec<usize>,
    pub witness: Vec<usize>,
    pub finished: bool,
}

impl Run {
    fn new(
        btor: Btor,
        mc: Vec<PropMcState>,
        ric3_proj: Ric3Proj,
        wsym: WlTsSymbol,
        cfg: RunConfig,
    ) -> anyhow::Result<Self> {
        let btorfe = BtorFrontend::new(btor.clone());
        fs::create_dir_all(ric3_proj.path("res"))?;
        recreate_dir(ric3_proj.path("tmp"))?;
        Ok(Self {
            btor,
            btorfe,
            wsym,
            ric3_proj,
            mc,
            nexus_task: None,
            cfg,
        })
    }

    pub(crate) fn run(&mut self) -> anyhow::Result<()> {
        self.launch_nexus();
        match self.cfg.ui.resolve() {
            RunUi::Tui => self.run_tui(),
            RunUi::Plain => self.run_plain(),
            _ => unreachable!(),
        }
    }

    pub(crate) fn process_updates(&mut self) -> anyhow::Result<RunUpdates> {
        let mut updates = RunUpdates::default();
        let Some(task) = self.nexus_task.take() else {
            return Ok(updates);
        };

        if let Err(err) = self.drain_nexus_channels(&task.state_trx, &task.wit_trx, &mut updates) {
            self.nexus_task = Some(task);
            return Err(err);
        }

        if task.join.is_finished() {
            let NexusTask {
                join,
                state_trx,
                wit_trx,
                ..
            } = task;
            let (res, _engine) = join
                .join()
                .map_err(|_| anyhow::anyhow!("PolyNexus worker thread panicked"))?;
            self.drain_nexus_channels(&state_trx, &wit_trx, &mut updates)?;
            self.apply_nexus_results(&res, &mut updates);
            updates.finished = true;
        } else {
            self.nexus_task = Some(task);
        }

        Ok(updates)
    }

    pub(crate) fn launch_nexus(&mut self) {
        let pending: Vec<usize> = self
            .mc
            .iter()
            .filter(|m| matches!(m.prop.res, McResult::Unknown(_)) && m.state == McStatus::Wait)
            .map(|m| m.prop.id)
            .collect();

        if pending.is_empty() {
            return;
        }

        let (ts, _) = self.btorfe.ts();
        let cfg = PolyNexusConfig {
            workers: self.cfg.workers.map(|workers| workers.get()),
            ..Default::default()
        };
        let mp_res: MpMcResult = self.mc.iter().map(|m| m.prop.res).collect();
        let mut engine = PolyNexus::new(cfg, ts, mp_res);

        let (state_tsx, state_trx) = state_channel_tracer();
        let (wit_tsx, wit_trx) = witness_channel_tracer();
        engine.add_tracer(Box::new(state_tsx));
        engine.add_tracer(Box::new(wit_tsx));
        let ctrl = engine.get_ctrl();

        for &id in &pending {
            self.mc[id].state = McStatus::Solving;
            self.mc[id].start_time = Some(Instant::now());
        }

        let join = spawn(move || {
            let res = MpEngine::check(&mut engine);
            (res, engine)
        });

        let ctrl = install_interrupt_handler(ctrl);

        self.nexus_task = Some(NexusTask {
            join,
            state_trx,
            wit_trx,
            ctrl,
        });
    }

    pub(crate) fn all_done(&self) -> bool {
        self.nexus_task.is_none()
            && self
                .mc
                .iter()
                .all(|m| !matches!(m.prop.res, McResult::Unknown(_)))
    }

    pub(crate) fn is_idle(&self) -> bool {
        self.nexus_task.is_none()
            && !self
                .mc
                .iter()
                .any(|m| matches!(m.prop.res, McResult::Unknown(_)) && m.state == McStatus::Wait)
    }

    fn drain_nexus_channels(
        &mut self,
        state_trx: &StateChannelTracerRx,
        wit_trx: &WitnessChannelTracerRx,
        updates: &mut RunUpdates,
    ) -> anyhow::Result<()> {
        while let std::result::Result::Ok((prop_id, result)) = state_trx.try_recv() {
            if let Some(prop_id) = prop_id {
                let prop = &mut self.mc[prop_id];
                prop.prop.res = result;
                if !matches!(result, McResult::Unknown(_)) {
                    if let Some(t) = prop.start_time.take() {
                        prop.time += t.elapsed();
                    }
                }
                updates.state.push(prop_id);
            }
        }
        while let std::result::Result::Ok(cex) = wit_trx.try_recv() {
            let cex = cex.into_sat().unwrap();
            let prop_id = cex.bad_id;
            let cex = self.btorfe.bl_certificate(McBlCertificate::SAT(cex));
            let wit_path = self.ric3_proj.path(format!("res/p{prop_id}.wit"));
            let wit = format!("{cex}");
            fs::write(&wit_path, &wit)?;

            let mut cex = self.btorfe.deserialize_wl_unsafe_certificate(wit);
            cex.enrich(&self.wsym.keys().cloned().collect());
            let vcd_path = self.ric3_proj.path(format!("res/p{prop_id}.vcd"));
            let vcd_file = BufWriter::new(File::create(vcd_path)?);
            crate::cli::vcd::wlwitness_vcd(&cex, &self.wsym, vcd_file, "")?;
            updates.witness.push(prop_id);
        }
        Ok(())
    }

    fn apply_nexus_results(&mut self, res: &MpMcResult, updates: &mut RunUpdates) {
        for (id, result) in res.iter().copied().enumerate() {
            let prop = &mut self.mc[id];
            let old_result = prop.prop.res;
            let old_state = prop.state;
            prop.prop.res = result;
            if matches!(result, McResult::Unknown(_)) {
                prop.state = McStatus::Pause;
            } else {
                prop.state = McStatus::Wait;
            }
            if old_state == McStatus::Solving && prop.state != McStatus::Solving {
                if let Some(t) = prop.start_time.take() {
                    prop.time += t.elapsed();
                }
            }
            if old_state != McStatus::Solving && prop.state == McStatus::Solving {
                prop.start_time = Some(Instant::now());
            }
            let changed = if matches!(result, McResult::Unknown(_)) {
                old_result != result || old_state != prop.state
            } else {
                old_result != result
            };
            if changed {
                updates.state.push(id);
            }
        }
    }
}

impl RunUi {
    fn resolve(self) -> Self {
        match self {
            RunUi::Auto if std::io::stdout().is_terminal() => RunUi::Tui,
            RunUi::Auto => RunUi::Plain,
            ui => ui,
        }
    }
}

pub fn run(cfg: RunConfig) -> anyhow::Result<()> {
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
                    start_time: None,
                    time: Duration::ZERO,
                })
                .collect()
        })
        .unwrap_or(PropMcState::default_from_wts(&wts, &symbol));
    let mut run = Run::new(btor, mc, ric3_proj, symbol, cfg)?;
    run.run()?;
    let res: Vec<_> = run.mc.iter().map(|l| l.prop.clone()).collect();
    run.ric3_proj.cache_res(res)?;
    Ok(())
}
