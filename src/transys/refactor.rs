use crate::transys::Transys;
use logicrs::VarVMap;

impl Transys {
    pub fn refactor(&self, map: &mut VarVMap) -> Self {
        println!("{}", self.rel);
        let (rel, m) = self.rel.topsort();
        *map = m.product(map);
        println!("{rel}");
        todo!()
    }
}
