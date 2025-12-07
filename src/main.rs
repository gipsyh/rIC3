#![feature(ptr_metadata)]

use clap::Parser;
use log::{error, info};
use rIC3::{
    Engine,
    bmc::BMC,
    config::{self, Config},
    frontend::{Frontend, aig::AigFrontend, btor::BtorFrontend},
    ic3::IC3,
    kind::Kind,
    portfolio::portfolio_main,
    rlive::Rlive,
    transys::TransysIf,
    wlbmc::WlBMC,
    wlkind::WlKind,
};
use std::{
    env, error, fs,
    mem::{self, transmute},
    process::exit,
    ptr,
};

fn interrupt_statistic(cfg: &Config, engine: &mut dyn Engine) {
    if cfg.interrupt_statistic {
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

fn main() -> Result<(), Box<dyn error::Error>> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .format_target(false)
        .init();
    fs::create_dir_all("/tmp/rIC3")?;
    let mut cfg = Config::parse();
    cfg.validate();
    cfg.model = cfg.model.canonicalize()?;
    info!("the model to be checked: {}", cfg.model.display());
    if let config::Engine::Portfolio = cfg.engine {
        portfolio_main(cfg);
        unreachable!();
    }
    let mut frontend: Box<dyn Frontend> = match cfg.model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => Box::new(AigFrontend::new(&cfg)),
        Some(ext) if (ext == "btor") | (ext == "btor2") => Box::new(BtorFrontend::new(&cfg)),
        _ => {
            error!("Error: unsupported file format");
            exit(1);
        }
    };
    let mut engine: Box<dyn Engine> = if cfg.engine.is_wl() {
        let (wts, _symbols) = frontend.wts();
        // info!("origin ts has {}", ts.statistic());
        match cfg.engine {
            config::Engine::WlBMC => Box::new(WlBMC::new(cfg.clone(), wts)),
            config::Engine::WlKind => Box::new(WlKind::new(cfg.clone(), wts)),
            _ => unreachable!(),
        }
    } else {
        let (ts, symbols) = frontend.ts();
        info!("origin ts has {}", ts.statistic());
        match cfg.engine {
            config::Engine::IC3 => Box::new(IC3::new(cfg.clone(), ts, symbols)),
            config::Engine::Kind => Box::new(Kind::new(cfg.clone(), ts)),
            config::Engine::BMC => Box::new(BMC::new(cfg.clone(), ts)),
            config::Engine::Rlive => Box::new(Rlive::new(cfg.clone(), ts)),
            _ => unreachable!(),
        }
    };
    interrupt_statistic(&cfg, engine.as_mut());
    let res = engine.check();
    engine.statistic();
    match res {
        Some(res) => {
            if res {
                if env::var("RIC3_WORKER").is_err() {
                    println!("UNSAT");
                }
                if cfg.witness {
                    println!("0");
                }
            } else if env::var("RIC3_WORKER").is_err() {
                println!("SAT");
            }
            certificate(&cfg, frontend.as_mut(), engine.as_mut(), res);
        }
        _ => {
            if env::var("RIC3_WORKER").is_err() {
                println!("UNKNOWN");
            }
            if cfg.witness {
                println!("2");
            }
        }
    }
    mem::forget(engine);
    if let Some(res) = res {
        exit(if res { 20 } else { 10 })
    } else {
        exit(30)
    }
}

pub fn certificate(cfg: &Config, frontend: &mut dyn Frontend, engine: &mut dyn Engine, res: bool) {
    if cfg.certificate.is_none() && !cfg.certify && (!cfg.witness || res) {
        return;
    }
    let certificate = if engine.is_wl() {
        if res {
            frontend.wl_safe_certificate(engine.wl_proof())
        } else {
            let witness = engine.wl_witness();
            debug_assert!(witness.state.len() == witness.input.len());
            frontend.wl_unsafe_certificate(witness)
        }
    } else if res {
        frontend.safe_certificate(engine.proof())
    } else {
        let witness = engine.witness();
        debug_assert!(witness.state.len() == witness.input.len());
        frontend.unsafe_certificate(witness)
    };
    if cfg.witness && !res {
        println!("{certificate}");
    }
    if let Some(cert_path) = &cfg.certificate {
        fs::write(cert_path, format!("{certificate}")).unwrap();
    }
    if cfg.certify {
        let certificate_file = tempfile::NamedTempFile::new().unwrap();
        let cert = certificate_file.path();
        fs::write(cert, format!("{certificate}")).unwrap();
        if frontend.certify(&cfg.model, cert) {
            info!("certificate verification passed");
        } else {
            error!("certificate verification failed");
            panic!();
        }
    }
}
