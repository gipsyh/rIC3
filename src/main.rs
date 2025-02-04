#![feature(ptr_metadata)]

use aig::Aig;
use clap::Parser;
use rIC3::{
    bmc::BMC,
    check_certifaiger, check_witness,
    frontend::aig::aig_preprocess,
    ic3::IC3,
    kind::Kind,
    options::{self, Options},
    portfolio::Portfolio,
    transys::Transys,
    verify_certifaiger, Engine,
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
    if options.verbose > 0 {
        println!("the model to be checked: {}", options.model);
    }
    let mut aig = if options.model.ends_with(".btor") || options.model.ends_with(".btor2") {
        panic!("rIC3 currently does not support parsing BTOR2 files. Please use btor2aiger (https://github.com/hwmcc/btor2tools) to first convert them to AIG format.")
    } else {
        Aig::from_file(&options.model)
    };
    if !aig.outputs.is_empty() && !options.certify {
        // not certifying, move outputs to bads
        // Move outputs to bads if no bad properties exist
        if aig.bads.is_empty() {
            aig.bads = std::mem::take(&mut aig.outputs);
            println!(
                "Warning: property not found, moved {} outputs to bad properties",
                aig.bads.len()
            );
        } else {
            println!("Warning: outputs are ignored");
        }
    }

    let origin_aig = aig.clone();
    if aig.bads.is_empty() {
        println!("warning: no property to be checked");
        verify_certifaiger(&aig, &options);
        exit(20);
    } else if aig.bads.len() > 1 {
        if options.certify {
            panic!("Error: Multiple properties detected. Cannot compress properties when certification is enabled.");
        }
        if options.verbose > 0 {
            println!("Warning: Multiple properties detected. rIC3 has compressed them into a single property.");
        }
        options.certify = false;
        aig.compress_property();
    }
    let mut engine: Box<dyn Engine> = if let options::Engine::Portfolio = options.engine {
        Box::new(Portfolio::new(options.clone(), &origin_aig))
    } else {
        let (aig, restore) = aig_preprocess(&aig, &options);
        let mut ts = Transys::from_aig(&aig, &restore);
        let pre_lemmas = vec![];
        if options.preprocess.sec {
            panic!("sec not support");
        }

        let assert_constrain = matches!(options.engine, options::Engine::IC3);
        let keep_dep = assert_constrain;
        ts = ts.simplify(&[], keep_dep, !assert_constrain);
        if options.verbose > 1 {
            ts.print_info();
        }
        let mut engine: Box<dyn Engine> = match options.engine {
            options::Engine::IC3 => Box::new(IC3::new(options.clone(), ts, pre_lemmas)),
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
        engine
    };
    let res = engine.check();
    if options.verbose > 0 {
        print!("result: ");
    }
    match res {
        Some(true) => {
            if options.verbose > 0 {
                println!("safe");
            }
            check_certifaiger(&mut engine, &origin_aig, &options)
        }
        Some(false) => {
            if options.verbose > 0 {
                println!("unsafe");
            }
            check_witness(&mut engine, &origin_aig, &options)
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
    if let options::Engine::Portfolio = options.engine {
        drop(engine);
    } else {
        mem::forget(engine);
    }
    if let Some(res) = res {
        exit(if res { 20 } else { 10 })
    } else {
        exit(0)
    }
}
