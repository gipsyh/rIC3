#![allow(non_snake_case)]
#![feature(get_mut_unchecked, likely_unlikely, ptr_metadata)]

pub mod bmc;
pub mod config;
pub mod frontend;
mod gipsat;
pub mod ic3;
pub mod kind;
pub mod portfolio;
pub mod rlive;
pub mod transys;
pub mod wlbmc;
pub mod wlkind;
pub mod wltransys;

use std::{
    env, fs,
    mem::{self, transmute},
    process::exit,
    ptr,
};

use crate::{
    bmc::BMC,
    frontend::{Frontend, aig::AigFrontend, btor::BtorFrontend, certificate_check},
    ic3::IC3,
    kind::Kind,
    rlive::Rlive,
    transys::{
        TransysIf,
        certify::{Proof, Witness},
    },
    wlbmc::WlBMC,
    wlkind::WlKind,
    wltransys::certify::{WlProof, WlWitness},
};
use config::Config;
use log::{error, info};

pub enum McResult {
    /// Safe
    Safe,
    /// Unsafe with Cex Depth
    Unsafe(usize),
    /// Bounded Proof if Some(depth)
    Unknown(Option<usize>),
}

pub trait Engine {
    fn check(&mut self) -> Option<bool>;

    fn statistic(&mut self) {}

    fn is_wl(&self) -> bool {
        false
    }

    fn proof(&mut self) -> Proof {
        panic!("unsupport proof");
    }

    fn witness(&mut self) -> Witness {
        panic!("unsupport witness");
    }

    fn wl_proof(&mut self) -> WlProof {
        assert!(self.is_wl());
        panic!("unsupport proof");
    }

    fn wl_witness(&mut self) -> WlWitness {
        assert!(self.is_wl());
        panic!("unsupport witness");
    }
}

pub fn ric3_check(cfg: Config) -> Option<bool> {
    let mut frontend: Box<dyn Frontend> = match cfg.model.extension() {
        Some(ext) if (ext == "aig") | (ext == "aag") => Box::new(AigFrontend::new(&cfg)),
        Some(ext) if (ext == "btor") | (ext == "btor2") => Box::new(BtorFrontend::new(&cfg)),
        _ => {
            error!("Unsupported file format. Supported extensions are: .aig, .aag, .btor, .btor2.");
            panic!();
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
    res
}

fn interrupt_statistic(cfg: &Config, engine: &mut dyn Engine) {
    if cfg.interrupt_statistic {
        let e: (usize, usize) = unsafe { transmute((engine as *mut dyn Engine).to_raw_parts()) };
        let _ = ctrlc::set_handler(move || {
            let e: *mut dyn Engine = unsafe {
                ptr::from_raw_parts_mut(
                    e.0 as *mut (),
                    transmute::<usize, std::ptr::DynMetadata<dyn Engine>>(e.1),
                )
            };
            let e = unsafe { &mut *e };
            e.statistic();
            exit(124);
        });
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
        certificate_check(cfg, cert);
    }
}
