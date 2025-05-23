#![feature(ptr_metadata)]

use clap::Parser;
use rIC3::{
    Engine,
    bmc::BMC,
    frontend::aig::AigFrontend,
    ic3::IC3,
    kind::Kind,
    options::{self, Options},
    portfolio::portfolio_main,
};
use std::{
    fs,
    mem::{self, transmute},
    process::exit,
    ptr,
};

fn main() {
    procspawn::init();
    fs::create_dir_all("/tmp/rIC3").unwrap();
    let mut options = Options::parse();
    options.model = options.model.canonicalize().unwrap();
    if options.verbose > 0 {
        println!("Info: the model to be checked: {}", options.model.display());
    }
    if let options::Engine::Portfolio = options.engine {
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
        options::Engine::IC3 => Box::new(IC3::new(options.clone(), ts, vec![])),
        options::Engine::Kind => Box::new(Kind::new(options.clone(), ts)),
        options::Engine::BMC => Box::new(BMC::new(options.clone(), ts)),
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
    if options.verbose > 0 {
        engine.statistic();
    }
    if options.verbose > 0 {
        print!("result: ");
    }
    match res {
        Some(true) => {
            if options.verbose > 0 {
                println!("safe");
            }
            if options.witness {
                println!("0");
            }
            aig.certificate(&mut engine, true)
        }
        Some(false) => {
            if options.verbose > 0 {
                println!("unsafe");
            }
            aig.certificate(&mut engine, false)
        }
        _ => {
            if options.verbose > 0 {
                println!("unknown");
            }
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
