use aig::Aig;
use btor::Btor;
use clap::Parser;
use log::{error, info};
use rIC3::{
    Engine, McResult,
    bmc::BMC,
    config::EngineConfig,
    frontend::{Frontend, aig::AigFrontend, btor::BtorFrontend, certificate_check},
    ic3::IC3,
    kind::Kind,
    portfolio::{Portfolio, PortfolioConfig},
    rlive::Rlive,
    tracer::LogTracer,
    transys::TransysIf,
    wlbmc::WlBMC,
    wlkind::WlKind,
};
use std::{env, fs, mem::transmute, path::PathBuf, process::exit, ptr};

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

    /// print witness when model is unsafe
    #[arg(long, default_value_t = false)]
    pub witness: bool,

    /// interrupt statistic
    #[arg(long, default_value_t = false)]
    pub interrupt_statistic: bool,
}

fn report_res(chk: &CheckConfig, res: McResult) {
    match res {
        McResult::Safe => {
            println!("UNSAT");
            if chk.witness {
                println!("0");
            }
        }
        McResult::Unsafe(_) => {
            println!("SAT");
            if chk.witness {
                let witness = fs::read_to_string(chk.cert.as_ref().unwrap()).unwrap();
                println!("{witness}");
            }
        }
        McResult::Unknown(_) => {
            println!("UNKNOWN");
            if chk.witness {
                println!("2");
            }
        }
    }
}

pub fn check(mut chk: CheckConfig, cfg: EngineConfig) -> anyhow::Result<()> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .format_target(false)
        .init();
    chk.model = chk.model.canonicalize()?;
    info!("the model to be checked: {}", chk.model.display());
    let mut tmp_cert = None;
    if chk.cert.is_none() && (chk.certify || chk.witness) {
        let tmp_cert_file = tempfile::NamedTempFile::new().unwrap();
        chk.cert = Some(PathBuf::from(tmp_cert_file.path()));
        tmp_cert = Some(tmp_cert_file);
    }
    if let EngineConfig::Portfolio(cfg) = cfg {
        let res = portfolio_main(chk, cfg);
        drop(tmp_cert);
        return res;
    }
    let mut frontend: Box<dyn Frontend> = match chk.model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => {
            let aig = Aig::from_file(&chk.model);
            Box::new(AigFrontend::new(aig))
        }
        Some(ext) if (ext == "btor") | (ext == "btor2") => {
            let btor = Btor::from_file(&chk.model);
            Box::new(BtorFrontend::new(btor))
        }
        _ => {
            error!("Unsupported file format. Supported extensions are: .aig, .aag, .btor, .btor2.");
            exit(1);
        }
    };
    let log_tracer = Box::new(LogTracer::new(cfg.as_ref()));
    let mut engine: Box<dyn Engine> = if cfg.is_wl() {
        let (wts, _symbols) = frontend.wts();
        // info!("origin ts has {}", ts.statistic());
        match cfg {
            EngineConfig::WlBMC(cfg) => Box::new(WlBMC::new(cfg, wts)),
            EngineConfig::WlKind(cfg) => Box::new(WlKind::new(cfg.clone(), wts)),
            _ => unreachable!(),
        }
    } else {
        let (ts, symbols) = frontend.ts();
        info!("origin ts has {}", ts.statistic());
        match cfg {
            EngineConfig::IC3(cfg) => Box::new(IC3::new(cfg.clone(), ts, symbols)),
            EngineConfig::Kind(cfg) => Box::new(Kind::new(cfg.clone(), ts)),
            EngineConfig::BMC(cfg) => Box::new(BMC::new(cfg.clone(), ts)),
            EngineConfig::Rlive(cfg) => Box::new(Rlive::new(cfg.clone(), ts)),
            _ => unreachable!(),
        }
    };
    engine.add_tracer(log_tracer);
    interrupt_statistic(&chk, engine.as_mut());
    let res = engine.check();
    engine.statistic();
    match res {
        McResult::Safe => {
            certificate(&chk, frontend.as_mut(), engine.as_mut(), true);
        }
        McResult::Unsafe(_) => {
            certificate(&chk, frontend.as_mut(), engine.as_mut(), false);
        }
        McResult::Unknown(_) => todo!(),
    }
    report_res(&chk, res);
    if chk.certify {
        assert!(certificate_check(&chk.model, chk.cert.as_ref().unwrap()));
    }
    drop(tmp_cert);
    Ok(())
}

fn interrupt_statistic(chk: &CheckConfig, engine: &mut dyn Engine) {
    if chk.interrupt_statistic {
        let e: (usize, usize) = unsafe { transmute((engine as *mut dyn Engine).to_raw_parts()) };
        let _ = ctrlc::set_handler(move || {
            let e: *mut dyn Engine = unsafe {
                ptr::from_raw_parts_mut(
                    e.0 as *mut (),
                    transmute::<usize, std::ptr::DynMetadata<dyn rIC3::Engine>>(e.1),
                )
            };
            let e = unsafe { &mut *e };
            e.statistic();
            exit(124);
        });
    }
}

pub fn certificate(
    chk: &CheckConfig,
    frontend: &mut dyn Frontend,
    engine: &mut dyn Engine,
    res: bool,
) {
    if chk.cert.is_none() {
        return;
    }
    let cert = if res {
        frontend.safe_certificate(engine.proof())
    } else {
        let witness = engine.witness();
        frontend.unsafe_certificate(witness)
    };
    fs::write(chk.cert.as_ref().unwrap(), format!("{cert}")).unwrap();
}

pub fn portfolio_main(chk: CheckConfig, cfg: PortfolioConfig) -> anyhow::Result<()> {
    let mut engine = Portfolio::new(chk.model.clone(), chk.cert.clone(), cfg);
    let res = engine.check();
    report_res(&chk, res);
    if chk.certify {
        assert!(certificate_check(&chk.model, chk.cert.as_ref().unwrap()));
    }
    Ok(())
}
