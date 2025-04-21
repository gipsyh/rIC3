use super::Frontend;
use crate::{options::Options, transys as bl, wl::transys::WlTransys};
use btor::Btor;
use std::process::exit;

pub struct BtorFrontend {
    origin_btor: Btor,
    origin_ts: WlTransys,
    opt: Options,
}

impl BtorFrontend {
    pub fn new(opt: &Options) -> Self {
        let mut origin_btor = Btor::from_file(&opt.model);
        let mut btor = origin_btor.clone();
        if btor.bad.is_empty() {
            if opt.verbose > 0 {
                println!("Warning: no property to be checked");
            }
            if let Some(certificate) = &opt.certificate {
                todo!()
                // btor.to_file(certificate, true);
            }
            exit(20);
        } else if btor.bad.len() > 1 {
            if opt.certify {
                panic!(
                    "Error: Multiple properties detected. Cannot compress properties when certification is enabled."
                );
            }
            if opt.verbose > 0 {
                println!(
                    "Warning: Multiple properties detected. rIC3 has compressed them into a single property."
                );
            }
            todo!()
        }
        let origin_ts = WlTransys::from_btor(&origin_btor);
        Self {
            origin_btor,
            origin_ts,
            opt: opt.clone(),
        }
    }
}

impl Frontend for BtorFrontend {
    fn ts(&mut self) -> bl::Transys {
        let mut ts = self.origin_ts.clone();
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

    fn certificate_safe(&mut self, engine: &mut dyn crate::Engine) {
        todo!()
    }

    fn certificate_unsafe(&mut self, engine: &mut dyn crate::Engine) {
        todo!()
    }
}
