use crate::{
    Engine,
    config::Config,
    wltransys::{WlTransys, certify::WlWitness, unroll::WlTransysUnroll},
};
use bitwuzla::Bitwuzla;
use giputils::hash::GHashMap;
use logicrs::fol::Term;

pub struct Ctilg {
    #[allow(unused)]
    cfg: Config,
    slv: Bitwuzla,
    uts: WlTransysUnroll,
    symbols: GHashMap<Term, String>,
}

impl Ctilg {
    pub fn new(cfg: Config, wts: WlTransys, symbols: GHashMap<Term, String>) -> Self {
        let mut slv = Bitwuzla::new();
        let mut uts = WlTransysUnroll::new(wts);
        uts.unroll_to(3);
        for k in 0..=uts.num_unroll {
            if k != uts.num_unroll {
                for b in uts.ts.bad.iter() {
                    slv.assert(&!uts.next(b, k));
                }
            }
            for c in uts.ts.constraint.iter() {
                slv.assert(&uts.next(c, k));
            }
        }

        Self {
            cfg,
            slv,
            uts,
            symbols,
        }
    }
}

impl Engine for Ctilg {
    fn is_wl(&self) -> bool {
        true
    }

    fn check(&mut self) -> Option<bool> {
        let mut res = true;
        for (i, b) in self.uts.ts.bad.iter().enumerate() {
            let nb = self.uts.next(b, self.uts.num_unroll);
            let r = self.slv.solve(&[nb]);
            res &= !r;
            println!(
                "The {}-th property{}is {}inductive.",
                i + 1,
                if let Some(s) = self.symbols.get(b) {
                    format!(" ({s}) ")
                } else {
                    " ".to_string()
                },
                if r { "NOT " } else { "" }
            );
        }
        Some(res)
    }

    fn wl_witness(&mut self) -> WlWitness {
        for b in self.uts.ts.bad.iter().rev() {
            let nb = self.uts.next(b, self.uts.num_unroll);
            if self.slv.solve(&[nb]) {
                return self.uts.witness(&mut self.slv);
            }
        }
        unreachable!()
    }
}
