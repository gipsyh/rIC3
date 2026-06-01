use crate::logger_init;
use anyhow::{Context, bail};
use clap::{ArgAction, Parser};
use log::info;
use rIC3::{
    BlEngine, Engine, McResult,
    config::EngineConfig,
    create_bl_engine, create_wl_engine,
    frontend::{certificate_check, frontend_from_model},
    portfolio::{Portfolio, PortfolioConfig},
    tracer::LogTracer,
    transys::TransysIf,
    ui::UiRenderer,
    utils::install_interrupt_handler,
};
use std::{env, fs, path::PathBuf, process::exit};

#[derive(Parser, Debug, Clone)]
pub struct CheckConfig {
    /// model file in aiger format or in btor2 format,
    /// for aiger model, the file name should be suffixed with .aig or .aag,
    /// for btor model, the file name should be suffixed with .btor or .btor2.
    pub model: PathBuf,

    /// certificate path
    #[arg(long)]
    pub cert: Option<PathBuf>,

    /// certify with certifaiger or cerbtora
    #[arg(long, default_value_t = false)]
    pub certify: bool,

    /// print counterexample when model is unsafe
    #[arg(long, default_value_t = false)]
    pub cex: bool,

    /// ui
    #[arg(long = "ui", action = ArgAction::Set, default_value_t = true)]
    pub ui: bool,

    /// interrupt statistic
    #[arg(long, default_value_t = false)]
    pub interrupt_statistic: bool,
}

fn report_res(chk: &CheckConfig, res: McResult) {
    match res {
        McResult::UNSAT => {
            println!("UNSAT");
            if chk.cex {
                println!("0");
            }
        }
        McResult::SAT(_) => {
            println!("SAT");
            if chk.cex {
                let cex = fs::read_to_string(chk.cert.as_ref().unwrap()).unwrap();
                println!("{cex}");
            }
        }
        McResult::Unknown(_) => {
            println!("UNKNOWN");
            if chk.cex {
                println!("2");
            }
        }
    }
}

pub fn check(mut chk: CheckConfig, cfg: EngineConfig) -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", if chk.ui { "warn" } else { "info" }) };
    }
    logger_init();
    if !chk.model.exists() {
        bail!("{} not found", chk.model.display());
    }
    chk.model = chk
        .model
        .canonicalize()
        .with_context(|| format!("failed to resolve model file: {}", chk.model.display()))?;
    info!("the model to be checked: {}", chk.model.display());
    let mut tmp_cert = None;
    if chk.cert.is_none() && (chk.certify || chk.cex) {
        let tmp_cert_file = tempfile::NamedTempFile::new().unwrap();
        chk.cert = Some(PathBuf::from(tmp_cert_file.path()));
        tmp_cert = Some(tmp_cert_file);
    }
    if let EngineConfig::Portfolio(cfg) = cfg {
        portfolio_main(chk, cfg)?;
        drop(tmp_cert);
        return Ok(());
    }
    let mut frontend = frontend_from_model(&chk.model)?;
    let res = if cfg.is_wl() {
        let (wts, _symbols) = frontend.wts();
        let mut engine = create_wl_engine(cfg.clone(), wts);
        engine.add_tracer(Box::new(LogTracer::new(cfg.as_ref())));
        let tui = chk.ui.then(|| UiRenderer::new(cfg.as_ref())).flatten();
        if let Some(tui) = tui.clone() {
            engine.add_tracer(Box::new(tui.clone()));
            engine.set_ui(tui);
        }
        let interrupt = install_interrupt_handler(engine.get_ctrl());
        let res = engine.check();
        engine.statistic();
        if interrupt.is_interrupted() {
            if let Some(tui) = tui {
                tui.finish(McResult::Unknown(None));
            }
            exit(130);
        }
        if let Some(cert_path) = &chk.cert {
            let cert = engine.certificate(res);
            let cert = frontend.wl_certificate(cert);
            fs::write(cert_path, format!("{cert}")).unwrap();
        }
        res
    } else {
        let (ts, symbols) = frontend.ts();
        info!("origin ts has {}", ts.statistic());
        let mut engine = create_bl_engine(cfg.clone(), ts, symbols);
        engine.add_tracer(Box::new(LogTracer::new(cfg.as_ref())));
        let tui = chk.ui.then(|| UiRenderer::new(cfg.as_ref())).flatten();
        if let Some(tui) = tui.clone() {
            engine.add_tracer(Box::new(tui.clone()));
            engine.set_ui(tui);
        }
        let interrupt = install_interrupt_handler(engine.get_ctrl());
        let res = engine.check();
        engine.statistic();
        if interrupt.is_interrupted() {
            if let Some(tui) = tui {
                tui.finish(McResult::Unknown(None));
            }
            exit(130);
        }
        if let Some(cert_path) = &chk.cert {
            let cert = engine.certificate(res);
            let cert = frontend.bl_certificate(cert);
            fs::write(cert_path, format!("{cert}")).unwrap();
        }
        res
    };
    report_res(&chk, res);
    if chk.certify {
        assert!(certificate_check(&chk.model, chk.cert.as_ref().unwrap()));
    }
    drop(tmp_cert);
    Ok(())
}

pub fn portfolio_main(chk: CheckConfig, cfg: PortfolioConfig) -> anyhow::Result<()> {
    let mut frontend = frontend_from_model(&chk.model)?;
    let (ts, symbols) = frontend.ts();
    info!("origin ts has {}", ts.statistic());
    let mut engine = Portfolio::new(ts, symbols, chk.cert.is_some(), cfg)?;
    if let Some(tui) = UiRenderer::new("Portfolio") {
        engine.set_ui(tui);
    }
    // Do not register the ctrlc interrupt handler here: it spawns a background
    // thread, and Portfolio::check forks workers afterwards. Forking after
    // threads have been spawned can deadlock in the child process.
    // let interrupt = install_interrupt_handler(engine.get_ctrl());
    let res = engine.check();
    // if interrupt.is_interrupted() {
    //     exit(130);
    // }
    if let Some(cert_path) = &chk.cert {
        let cert = engine.certificate(res);
        let cert = frontend.bl_certificate(cert);
        fs::write(cert_path, format!("{cert}")).unwrap();
    }
    report_res(&chk, res);
    if chk.certify {
        assert!(certificate_check(&chk.model, chk.cert.as_ref().unwrap()));
    }
    Ok(())
}
