use rIC3::McResult;
use std::collections::HashMap;

pub struct Prop {
    id: usize,
    name: String,
}

pub struct PropResult {
    engine: String,
    res: McResult,
}

pub struct RiceResult {
    res: HashMap<Prop, PropResult>,
}

