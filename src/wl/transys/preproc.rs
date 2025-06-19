use super::WlTransys;
use logicrs::fol::op::Ite;

impl WlTransys {
    pub fn remove_reset(&mut self) {
        if self.constraint.len() > 0 {
            return;
        }
        let mut reset = None;
        for (l, _) in self.init.iter() {
            let n = self.next(l);
            let op = n.try_op_term().unwrap();
            if op.op == Ite {
                let Some(v) = op[0].try_var_term() else {
                    return;
                };
                match reset {
                    Some(rv) if rv != v => return,
                    None => reset = Some(v),
                    _ => {}
                }
            }
        }
        dbg!(reset);
    }
}
