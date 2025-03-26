use crate::{bmc::BMC, ic3::IC3, options::Options, wl::transys::Transys, Engine};
use btor::Btor;

pub fn test(options: Options) {
    let btor = Btor::new(&options.model);
    let mut ts = Transys::new(&btor);
    ts.print_info();
    for _ in 0..3 {
        ts.coi_refine();
        ts.simplify();
        ts.print_info();
    }
    // ts.remove_reset();
    let mut bitblast = ts.bitblast();
    for _ in 0..3 {
        bitblast.coi_refine();
        bitblast.simplify();
        bitblast.print_info();
    }
    let ts = bitblast.to_bit_level();
    let bmc = true;
    let ts = ts.simplify(&[], !bmc, bmc);
    ts.print_info();
    if bmc {
        let mut engine = BMC::new(options, ts);
        dbg!(engine.check());
    } else {
        let mut engine = IC3::new(options, ts, vec![]);
        dbg!(engine.check());
    }
}
