use crate::cli::{Ric3Config, rproj::Ric3Proj, yosys::Yosys};
use btor::Btor;
use giputils::file::recreate_dir;
use rIC3::frontend::{Frontend, btor::BtorFrontend};
use rIC3::wltransys::symbol::link_wts_by_symbol;
use rIC3::wltransys::transform::WlTransform;
use rIC3::wltransys::{WlTransys, symbol::WlTsSymbol};

pub fn link_candinv(
    core_wts: &WlTransys,
    core_wsym: &WlTsSymbol,
    candinv_bf: &mut BtorFrontend,
) -> anyhow::Result<(WlTransys, WlTsSymbol)> {
    let (mut candinv_wts, mut candinv_wsym) = candinv_bf.wts();
    let candinv_tf = candinv_wts.simplify(&mut vec![]);
    candinv_tf.trans_sym(&mut candinv_wsym);

    let (linked_wts, linked_wsym, mut unlinked_symbols) =
        link_wts_by_symbol(core_wts, core_wsym, candinv_wts, candinv_wsym)?;
    unlinked_symbols.retain(|s| !s.starts_with("invariants."));
    if !unlinked_symbols.is_empty() {
        println!("Unlinked candinv signals: {}", unlinked_symbols.join(","));
    }
    Ok((linked_wts, linked_wsym))
}

pub fn synthesis_candinv(rcfg: &Ric3Config, rp: &Ric3Proj) -> anyhow::Result<BtorFrontend> {
    let candinv = rcfg
        .formal
        .as_ref()
        .and_then(|formal| formal.invariants.clone())
        .ok_or_else(|| anyhow::anyhow!("missing required config: formal.invariants"))?;
    let shadow = rp.path("cill/shadow.sv");

    let candinv_dir = rp.path("cill/candinv");
    recreate_dir(&candinv_dir)?;
    Yosys::generate_btor_with_files(&rcfg, &[shadow, candinv], &candinv_dir, "invariants", true)?;
    Ok(BtorFrontend::new(Btor::from_file(
        candinv_dir.join("invariants.btor"),
    )))
}
