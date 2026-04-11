use crate::config::{EngineConfig, EngineConfigBase};
use crate::frontend::Frontend;
use crate::tracer::{
    PipeStateTracerRecv, PipeTracerRecv, PipeTracerSend, Tracer, TracerIf, pipe_tracer,
};
use crate::transys::Transys;
use crate::{Engine, EngineCtrl, McResult, create_bl_engine, impl_config_deref};
use anyhow::{Context, bail};
use clap::{Args, Parser};
use giputils::hash::GHashMap;
use giputils::logger::with_log_level;
use log::{LevelFilter, info, set_max_level};
use logicrs::VarSymbols;
use mio::unix::SourceFd;
use mio::{Events, Interest, Poll, Registry, Token};
use nix::errno::Errno;
use nix::sys::wait::{WaitPidFlag, WaitStatus, waitpid};
use nix::unistd::Pid;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use std::iter;
use std::os::fd::AsRawFd;
use std::time::{Duration, Instant};
use std::{path::PathBuf, process::exit, sync::mpsc, thread::spawn};
use tempfile::{NamedTempFile, TempDir};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct PortfolioConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    /// worker configuration
    #[arg(long = "config")]
    pub config: Option<String>,
    // /// woker memory limit in GB
    // #[arg(long = "worker-mem-limit", default_value_t = 16)]
    // pub wmem_limit: usize,
}

impl_config_deref!(PortfolioConfig);

impl Default for PortfolioConfig {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "portfolio"]);
        cfg.into_portfolio().unwrap()
    }
}

pub struct Portfolio {
    ts: Transys,
    sym: VarSymbols,
    frontend: Box<dyn Frontend>,
    cert: Option<PathBuf>,
    cfg: PortfolioConfig,
    engines: Vec<Worker>,
    running: GHashMap<Pid, usize>,
    winner_idx: Option<usize>,
    ctrl: EngineCtrl,
    tracer: Tracer,
    #[allow(unused)]
    temp_dir: TempDir,
}

struct Worker {
    name: String,
    cfg: EngineConfig,
    args: String,
    cert: Option<NamedTempFile>,
    trace: Option<PipeTracerRecv>,
    state: McResult,
}

impl Worker {
    fn run(
        &self,
        ts: &Transys,
        sym: &VarSymbols,
        frontend: &mut dyn Frontend,
        tracer: PipeTracerSend,
    ) -> ! {
        set_max_level(LevelFilter::Warn);
        // We are already in the forked child, so take ownership of the inherited
        // in-memory model directly instead of reparsing or serializing it.
        let ts = unsafe { std::ptr::read(ts) };
        let sym = unsafe { std::ptr::read(sym) };
        let mut engine = create_bl_engine(self.cfg.clone(), ts, sym);
        engine.add_tracer(Box::new(tracer));
        let res = engine.check();
        write_certificate(
            frontend,
            engine.as_mut(),
            self.cert.as_ref().map(|c| c.path()),
            res,
        );
        exit(0);
    }
}

fn write_certificate(
    frontend: &mut dyn Frontend,
    engine: &mut dyn Engine,
    cert: Option<&std::path::Path>,
    res: McResult,
) {
    let Some(cert_path) = cert else {
        return;
    };
    let certificate = match res {
        McResult::Safe => frontend.safe_certificate(engine.proof()),
        McResult::Unsafe(_) => frontend.unsafe_certificate(engine.witness()),
        McResult::Unknown(_) => return,
    };
    std::fs::write(cert_path, format!("{certificate}")).unwrap();
}

impl Portfolio {
    pub fn new(
        frontend: Box<dyn Frontend>,
        ts: Transys,
        sym: VarSymbols,
        cert: Option<PathBuf>,
        cfg: PortfolioConfig,
    ) -> anyhow::Result<Self> {
        let temp_dir = tempfile::TempDir::new_in("/tmp/rIC3/").unwrap();
        let mut engines = Vec::new();
        let mut new_engine = |name, args: &str| {
            let argv: Vec<_> = iter::once("").chain(args.split_whitespace()).collect();
            let cfg = EngineConfig::try_parse_from(argv)?;
            assert!(!cfg.is_wl());
            let cert = if cert.is_some() {
                let certificate = NamedTempFile::new_in(temp_dir.path()).unwrap();
                Some(certificate)
            } else {
                None
            };
            engines.push(Worker {
                name,
                cfg,
                args: args.to_string(),
                cert,
                trace: None,
                state: McResult::default(),
            });
            anyhow::Ok(())
        };
        let portfolio_toml = include_str!("portfolio.toml");
        let portfolio_config: GHashMap<String, GHashMap<String, String>> =
            toml::from_str(portfolio_toml).unwrap();
        let config = cfg.config.as_deref().unwrap_or("bl_default");
        let Some(worker_cfgs) = portfolio_config.get(config) else {
            bail!("unknown portfolio config `{config}`");
        };
        for (name, args) in worker_cfgs.iter() {
            new_engine(name.clone(), args)
                .with_context(|| format!("invalid portfolio worker `{name}`"))?;
        }
        Ok(Self {
            ts,
            sym,
            frontend,
            cert,
            cfg,
            engines,
            running: GHashMap::new(),
            winner_idx: None,
            temp_dir,
            ctrl: EngineCtrl::new(),
            tracer: Tracer::new(),
        })
    }

    fn terminate_running(&mut self) {
        for &pid in self.running.keys() {
            let _ = nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGTERM);
        }
        loop {
            match waitpid(None, None) {
                Ok(WaitStatus::Exited(pid, code)) => {
                    let worker_idx = self.running.remove(&pid).unwrap();
                    if code != 0 {
                        info!("{} exited with code {code}", self.engines[worker_idx].name);
                    }
                }
                Ok(WaitStatus::Signaled(pid, _, _)) => {
                    self.running.remove(&pid);
                }
                Err(Errno::EINTR) => continue,
                Err(Errno::ECHILD) => {
                    assert!(self.running.is_empty());
                    return;
                }
                Err(err) => panic!("portfolio waitpid failed: {err}"),
                _ => panic!(),
            }
        }
    }

    pub fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn on_state_trace(&mut self, worker_idx: usize, prop: Option<usize>, res: McResult) {
        let worker = &mut self.engines[worker_idx];
        worker.state = res;
        self.tracer.trace_state(prop, res);
        let prop_prefix = prop.map(|p| format!("p{p}: ")).unwrap_or_default();
        match res {
            McResult::Safe => info!("{}{} proved the property", worker.name, prop_prefix),
            McResult::Unsafe(d) => info!(
                "{}{} found a counterexample at depth {d}",
                worker.name, prop_prefix
            ),
            McResult::Unknown(Some(d)) => {
                info!(
                    "{}{} found no counterexample at depth {d}",
                    worker.name, prop_prefix
                );
            }
            McResult::Unknown(None) => {}
        }
    }

    fn reap_child(&mut self) -> Option<McResult> {
        loop {
            match waitpid(None, Some(WaitPidFlag::WNOHANG)) {
                Ok(WaitStatus::StillAlive) => break,
                Ok(WaitStatus::Exited(pid, code)) => {
                    let worker_idx = self.running[&pid];
                    self.running.remove(&pid);
                    let worker = &mut self.engines[worker_idx];
                    if code == 0 {
                        if self.winner_idx.is_none() {
                            info!(
                                "best worker: {}, configuration: {}",
                                worker.name, worker.args
                            );
                            self.winner_idx = Some(worker_idx);
                            if let Some(cert) = &self.cert {
                                let _ = std::fs::copy(worker.cert.as_ref().unwrap().path(), cert);
                            }
                            while let Some((prop, res)) = self.engines[worker_idx]
                                .trace
                                .as_mut()
                                .map(|t| t.state_recv())
                                .and_then(PipeStateTracerRecv::try_recv)
                            {
                                self.on_state_trace(worker_idx, prop, res);
                            }
                            let res = self.engines[worker_idx].state;
                            assert!(!res.is_unknown());
                            return Some(res);
                        }
                    } else {
                        info!("{} exited with code {code}", worker.name);
                    }
                }
                Ok(WaitStatus::Signaled(pid, _, _)) => {
                    self.running.remove(&pid);
                }
                Err(Errno::EINTR) => continue,
                Err(Errno::ECHILD) => break,
                Err(err) => panic!("portfolio waitpid failed: {err}"),
                _ => panic!(),
            }
        }
        None
    }

    fn on_trace_ready(&mut self, registry: &Registry, pid: Pid, event: &mio::event::Event) {
        let Some(&worker_idx) = self.running.get(&pid) else {
            return;
        };
        while let Some((prop, res)) = {
            let worker = &mut self.engines[worker_idx];
            worker
                .trace
                .as_mut()
                .map(|t| t.state_recv())
                .and_then(PipeStateTracerRecv::try_recv)
        } {
            self.on_state_trace(worker_idx, prop, res);
        }

        if event.is_error() || event.is_read_closed() || event.is_write_closed() {
            let mut trace = {
                let worker = &mut self.engines[worker_idx];
                worker.trace.take()
            };
            if let Some(trace) = trace.as_mut() {
                Self::deregister_trace_pipe(registry, trace);
            }
        }
    }

    fn register_trace_pipe(registry: &Registry, pid: Pid, trace: &mut PipeTracerRecv) {
        let raw_fd = trace.state_recv().pipe().as_raw_fd();
        let mut source = SourceFd(&raw_fd);
        registry
            .register(
                &mut source,
                Token(pid.as_raw() as usize),
                Interest::READABLE,
            )
            .expect("portfolio mio register failed");
    }

    fn deregister_trace_pipe(registry: &Registry, trace: &mut PipeTracerRecv) {
        let raw_fd = trace.state_recv().pipe().as_raw_fd();
        let mut source = SourceFd(&raw_fd);
        let _ = registry.deregister(&mut source);
    }

    pub fn check(&mut self) -> McResult {
        let mut poll = Poll::new().unwrap();
        for worker_idx in 0..self.engines.len() {
            let (tracer_send, mut tracer_recv) = pipe_tracer(true, false, false);
            let worker = &mut self.engines[worker_idx];
            match fork::fork().unwrap() {
                fork::Fork::Parent(child) => {
                    drop(tracer_send);
                    let pid = Pid::from_raw(child);
                    info!("start engine {}", worker.name);
                    Self::register_trace_pipe(poll.registry(), pid, &mut tracer_recv);
                    worker.trace = Some(tracer_recv);
                    self.running.insert(pid, worker_idx);
                }
                fork::Fork::Child => {
                    drop(tracer_recv);
                    worker.run(&self.ts, &self.sym, self.frontend.as_mut(), tracer_send);
                }
            }
        }

        let start = Instant::now();
        let mut events = Events::with_capacity(self.engines.len());
        loop {
            if self.ctrl.is_terminated() || self.cfg.time_limit_hit(start) {
                self.terminate_running();
                return McResult::Unknown(None);
            }

            if let Some(res) = self.reap_child() {
                self.terminate_running();
                return res;
            }

            match poll.poll(&mut events, Some(Duration::from_millis(100))) {
                Ok(()) => {
                    for event in &events {
                        let pid = Pid::from_raw(event.token().0 as i32);
                        self.on_trace_ready(poll.registry(), pid, event);
                    }
                }
                Err(err) => panic!("portfolio mio poll failed: {err}"),
            }

            if self.running.is_empty() {
                return self
                    .winner_idx
                    .map(|winner_idx| self.engines[winner_idx].state)
                    .unwrap_or(McResult::Unknown(None));
            }
        }
    }

    pub fn get_ctrl(&self) -> EngineCtrl {
        self.ctrl.clone()
    }
}

#[derive(Default, Clone)]
pub struct LightPortfolioConfig {
    pub time_limit: Option<usize>,
}

pub struct LightPortfolio {
    ts: Transys,
    sym: VarSymbols,
    cfg: LightPortfolioConfig,
    ecfgs: Vec<EngineConfig>,
    engines: Vec<Box<dyn Engine>>,
    ctrl: EngineCtrl,
}

impl LightPortfolio {
    pub fn new(
        cfg: LightPortfolioConfig,
        ts: Transys,
        sym: VarSymbols,
        ecfgs: Vec<EngineConfig>,
    ) -> Self {
        Self {
            cfg,
            ecfgs,
            ts,
            sym,
            engines: Vec::new(),
            ctrl: EngineCtrl::new(),
        }
    }
}

impl Engine for LightPortfolio {
    fn check(&mut self) -> McResult {
        let engines: Vec<_> = self
            .ecfgs
            .clone()
            .into_par_iter()
            .map(|ecfg| create_bl_engine(ecfg, self.ts.clone(), self.sym.clone()))
            .collect();
        let ctrls: Vec<_> = engines.iter().map(|e| e.get_ctrl()).collect();
        let (tx, rx) = mpsc::channel();
        let mut joins = Vec::new();
        with_log_level(log::LevelFilter::Warn, || {
            let start = Instant::now();
            let num_engines = engines.len();
            for mut e in engines {
                let tx = tx.clone();
                let join = spawn(move || {
                    let res = e.check();
                    let _ = tx.send(res);
                    (e, res)
                });
                joins.push(join);
            }
            let mut res = McResult::Unknown(None);
            let mut finished = 0;
            while finished < num_engines {
                if self.ctrl.is_terminated() {
                    info!("LightPortfolio interrupted by external signal.");
                    break;
                }
                if let Some(t) = self.cfg.time_limit
                    && start.elapsed().as_secs() >= t as u64
                {
                    info!("LightPortfolio terminated by timeout.");
                    break;
                }
                match rx.recv_timeout(std::time::Duration::from_millis(100)) {
                    Ok(r) => {
                        finished += 1;
                        if !r.is_unknown() {
                            res = r;
                            break;
                        }
                    }
                    Err(mpsc::RecvTimeoutError::Timeout) => continue,
                    Err(mpsc::RecvTimeoutError::Disconnected) => {
                        break;
                    }
                }
            }
            for c in ctrls {
                c.terminate();
            }
            for j in joins {
                let (e, _) = j.join().unwrap();
                self.engines.push(e);
            }
            res
        })
    }

    fn get_ctrl(&self) -> EngineCtrl {
        self.ctrl.clone()
    }
}
