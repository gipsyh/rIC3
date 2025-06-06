#![feature(ptr_metadata)]

use clap::Parser;
use log::{error, info};
use rIC3::{
    Engine,
    bmc::BMC,
    config::{self, Config},
    frontend::aig::AigFrontend,
    ic3::IC3,
    kind::Kind,
    portfolio::portfolio_main,
};
use std::{
    env, fs,
    mem::{self, transmute},
    process::exit,
    ptr,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    procspawn::init();
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .format_target(false)
        .init();
    fs::create_dir_all("/tmp/rIC3")?;
    let mut cfg = Config::parse();
    cfg.model = cfg.model.canonicalize()?;
    info!("the model to be checked: {}", cfg.model.display());
    if let config::Engine::Portfolio = cfg.engine {
        portfolio_main(cfg);
        unreachable!();
    }
    let mut aig = match cfg.model.extension() {
        Some(ext) if (ext == "btor") | (ext == "btor2") => {
            error!(
                "rIC3 currently does not support parsing BTOR2 files. Please use btor2aiger (https://github.com/hwmcc/btor2tools) to first convert them to AIG format."
            );
            exit(1);
        }
        Some(ext) if (ext == "aig") | (ext == "aag") => AigFrontend::new(&cfg),
        _ => {
            error!("Error: unsupported file format");
            exit(1);
        }
    };
    let ts = aig.ts();
    if cfg.preprocess.sec {
        panic!("Error: sec not support");
    }
    let mut engine: Box<dyn Engine> = match cfg.engine {
        config::Engine::IC3 => Box::new(IC3::new(cfg.clone(), ts, vec![])),
        config::Engine::Kind => Box::new(Kind::new(cfg.clone(), ts)),
        config::Engine::BMC => Box::new(BMC::new(cfg.clone(), ts)),
        config::Engine::Portfolio => unreachable!(),
    };
    if cfg.interrupt_statistic {
        let e: (usize, usize) =
            unsafe { transmute((engine.as_mut() as *mut dyn Engine).to_raw_parts()) };
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
    let res = engine.check();
    engine.statistic();
    match res {
        Some(true) => {
            if env::var("RIC3_WORKER").is_err() {
                println!("result: safe");
            }
            if cfg.witness {
                println!("0");
            }
            aig.certificate(&mut engine, true)
        }
        Some(false) => {
            if env::var("RIC3_WORKER").is_err() {
                println!("result: unsafe");
            }
            aig.certificate(&mut engine, false)
        }
        _ => {
            if env::var("RIC3_WORKER").is_err() {
                println!("result: unknown");
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
