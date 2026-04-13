use crate::logger_init;
use clap::Parser;
use log::info;
use rIC3::{
    Engine, McResult,
    config::EngineConfig,
    create_bl_engine, create_wl_engine,
    frontend::{certificate_check, frontend_from_model},
    portfolio::{Portfolio, PortfolioConfig},
    tracer::LogTracer,
    transys::TransysIf,
};
use std::{env, fs, mem::transmute, path::PathBuf, process::exit};

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

    /// interrupt statistic
    #[arg(long, default_value_t = false)]
    pub interrupt_statistic: bool,
}

fn report_res(chk: &CheckConfig, res: McResult) {
    match res {
        McResult::Satisfied => {
            println!("Satisfied");
            if chk.cex {
                println!("0");
            }
        }
        McResult::Violated(_) => {
            println!("Violated");
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
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    logger_init();
    chk.model = chk.model.canonicalize()?;
    info!("the model to be checked: {}", chk.model.display());
    let mut tmp_cert = None;
    if chk.cert.is_none() && (chk.certify || chk.cex) {
        let tmp_cert_file = tempfile::NamedTempFile::new().unwrap();
        chk.cert = Some(PathBuf::from(tmp_cert_file.path()));
        tmp_cert = Some(tmp_cert_file);
    }
    if let EngineConfig::Portfolio(cfg) = cfg {
        let res = portfolio_main(chk, cfg);
        drop(tmp_cert);
        return res;
    }
    let mut frontend = frontend_from_model(&chk.model)?;
    let res = if cfg.is_wl() {
        let (wts, _symbols) = frontend.wts();
        let mut engine = create_wl_engine(cfg.clone(), wts);
        engine.add_tracer(Box::new(LogTracer::new(cfg.as_ref())));
        interrupt_statistic(&chk, engine.as_mut());
        let res = engine.check();
        engine.statistic();
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
        interrupt_statistic(&chk, engine.as_mut());
        let res = engine.check();
        engine.statistic();
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

fn interrupt_statistic(chk: &CheckConfig, engine: &mut dyn Engine) {
    if chk.interrupt_statistic {
        let e: [usize; 2] = unsafe { transmute(engine as *mut dyn Engine) };
        let _ = ctrlc::set_handler(move || {
            let e: *mut dyn Engine = unsafe { transmute(e) };
            let e = unsafe { &mut *e };
            e.statistic();
            exit(124);
        });
    }
}

pub fn portfolio_main(chk: CheckConfig, cfg: PortfolioConfig) -> anyhow::Result<()> {
    let mut frontend = frontend_from_model(&chk.model)?;
    let (ts, symbols) = frontend.ts();
    info!("origin ts has {}", ts.statistic());
    let mut engine = Portfolio::new(frontend, ts, symbols, chk.cert.clone(), cfg)?;
    let res = engine.check();
    report_res(&chk, res);
    if chk.certify {
        assert!(certificate_check(&chk.model, chk.cert.as_ref().unwrap()));
    }
    Ok(())
}
