use clap::Parser;
use log::info;
use rIC3::{
    config::{self, Config},
    portfolio::portfolio_main,
    ric3_check,
};
use std::{env, error, fs, process::exit};

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
    let res = ric3_check(cfg.clone());
    if let Some(res) = res {
        exit(if res { 20 } else { 10 })
    } else {
        exit(30)
    }
}
