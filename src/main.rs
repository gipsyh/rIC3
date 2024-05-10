use clap::Parser;
use rIC3::{Args, IC3};

fn main() {
    let mut args = Args::parse();
    let aig = "../mc-benchmark/hwmcc1920/aig-1.8/cal149.aag";
    if args.model.is_none() {
        args.model = Some(aig.to_string());
    }

    let mut ic3 = IC3::new(args);
    println!("result: {}", ic3.check_with_int_hanlder());
}
