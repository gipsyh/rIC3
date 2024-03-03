use clap::Parser;
use ic3::{Args, Ic3};

fn main() {
    let mut args = Args::parse();
    let aig = "../mc-benchmark/hwmcc1920/aig-1.8/cal149.aag";
    if args.model.is_none() {
        args.model = Some(aig.to_string());
    }

    let mut ic3 = Ic3::new(args);
    println!("result: {}", ic3.check_with_int_hanlder());
}
