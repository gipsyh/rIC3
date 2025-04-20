use btor::Btor;
use crate::{transys as bl, wl::transys::Transys};

pub fn btor2ts(btor: Btor) -> bl::Transys {
    let mut ts = Transys::new(&btor);
    // ts.print_info();
    for _ in 0..3 {
        ts.coi_refine();
        ts.simplify();
        // ts.print_info();
    }
    // ts.remove_reset();
    let mut bitblast = ts.bitblast();
    for _ in 0..3 {
        bitblast.coi_refine();
        bitblast.simplify();
        // bitblast.print_info();
    }
    bitblast.to_bit_level()
}