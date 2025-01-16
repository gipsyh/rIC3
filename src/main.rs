use aig::Aig;
use clap::Parser;
use rIC3::{Options, IC3};
use std::collections::HashMap;
use transys::Transys;

fn main() {
    let args = Options::parse();
    let aig = Aig::from_file(&args.model);
    let rst = HashMap::new();
    let mut ts = Transys::from_aig(&aig, &rst);
    ts = ts.simplify(&[], true, false);

    let mut ic3 = IC3::new(args, ts);
    println!("result: {}", ic3.check_with_int_hanlder());
}
