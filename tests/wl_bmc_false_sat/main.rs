#[path = "../it.rs"]
mod it;

use logicrs::fol::{Sort, Term};
use rIC3::wltransys::{WlTransys, unroll::WlTransysUnroll};
use std::path::Path;

#[test]
fn unrolling_a_toggle_preserves_every_frame() {
    let latch = Term::new_var(Sort::bool());
    let mut ts = WlTransys::default();
    ts.add_latch(latch.clone(), Some(Term::bool_const(false)), !&latch);
    let mut unroll = WlTransysUnroll::new(ts);
    unroll.unroll_to(4);
    for depth in 0..=4 {
        let expected = if depth % 2 == 0 {
            latch.clone()
        } else {
            !&latch
        };
        assert_eq!(unroll.next(&latch, depth), expected, "depth {depth}");
    }
}

// https://github.com/gipsyh/rIC3/issues/209
// Run with: RUST_LOG=info cargo test --release --test wl_bmc_false_sat -- --nocapture
#[test]
#[ignore = "wlbmc"]
fn wl_bmc_agrees_with_bmc_through_depth_11() {
    let model = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/wl_bmc_false_sat/vgasim_imgfifo-p040.btor2");

    // The bit-level engine rules out a counterexample through depth 11.
    it::check(&model, &["bmc", "--end", "11"], "UNKNOWN", false);
    it::check(&model, &["wl-bmc", "--end", "10"], "UNKNOWN", false);

    // #209 incorrectly reported SAT at depth 11, even without --cex.
    it::check(&model, &["wl-bmc", "--end", "11"], "UNKNOWN", false);
}
