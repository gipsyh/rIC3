mod it;

use it::check;
use std::path::Path;

#[test]
fn counter_is_sat() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for file in ["counter.aig", "counter.btor"] {
        let model = root.join("examples/counter").join(file);
        for engine in ["ic3", "bmc"] {
            check(&model, &[engine], "SAT");
        }
    }
}
