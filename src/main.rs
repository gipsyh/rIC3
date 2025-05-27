#![feature(ptr_metadata)]

use clap::Parser;
use log::info;
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

fn main() {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    procspawn::init();
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .init();
    fs::create_dir_all("/tmp/rIC3").unwrap();
    let mut options = Config::parse();
    options.model = options.model.canonicalize().unwrap();
    info!("the model to be checked: {}", options.model.display());
    if let config::Engine::Portfolio = options.engine {
        portfolio_main(options);
        unreachable!();
    }
    let mut aig = match options.model.extension() {
        Some(ext) if (ext == "btor") | (ext == "btor2") => panic!(
            "Error: rIC3 currently does not support parsing BTOR2 files. Please use btor2aiger (https://github.com/hwmcc/btor2tools) to first convert them to AIG format."
        ),
        Some(ext) if (ext == "aig") | (ext == "aag") => AigFrontend::new(&options),
        _ => panic!("Error: unsupported file format"),
    };
    let ts = aig.ts();
    if options.preprocess.sec {
        panic!("Error: sec not support");
    }
    let mut engine: Box<dyn Engine> = match options.engine {
        config::Engine::IC3 => Box::new(IC3::new(options.clone(), ts, vec![])),
        config::Engine::Kind => Box::new(Kind::new(options.clone(), ts)),
        config::Engine::BMC => Box::new(BMC::new(options.clone(), ts)),
        _ => unreachable!(),
    };
    if options.interrupt_statistic {
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
            println!("result: safe");
            if options.witness {
                println!("0");
            }
            aig.certificate(&mut engine, true)
        }
        Some(false) => {
            println!("result: unsafe");
            aig.certificate(&mut engine, false)
        }
        _ => {
            println!("result: unknown");
            if options.witness {
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
