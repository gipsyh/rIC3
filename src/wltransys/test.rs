#[cfg(test)]
mod tests {
    use super::super::*;
    use giputils::bitvec::BitVec;
    use logicrs::fol::{Sort, term_mgr};

    #[test]
    fn wltransys_round_trip_by_term_id() {
        let input = Term::new_var(Sort::Bv(4));
        let latch = Term::new_var(Sort::Bv(4));
        let init = Term::bv_const(BitVec::zero(4));
        let next = &input + &latch;
        let bad = input.teq(&latch);

        let wts = WlTransys {
            input: vec![input.clone()],
            latch: vec![latch.clone()],
            init: GHashMap::from_iter([(latch.clone(), init.clone())]),
            next: GHashMap::from_iter([(latch.clone(), next.clone())]),
            bad: vec![bad.clone()],
            output: vec![next.clone()],
            constraint: vec![Term::bool_const(true)],
            justice: vec![bad.clone()],
        };

        let content = ron::to_string(&wts).unwrap();
        term_mgr().enable_id_map();
        let restored: WlTransys = ron::from_str(&content).unwrap();

        assert_eq!(restored.input, vec![input]);
        assert_eq!(restored.latch, vec![latch.clone()]);
        assert_eq!(restored.init[&latch], init);
        assert_eq!(restored.next[&latch], next);
        assert_eq!(restored.bad, vec![bad.clone()]);
        assert_eq!(restored.output, vec![next]);
        assert_eq!(restored.constraint, vec![Term::bool_const(true)]);
        assert_eq!(restored.justice, vec![bad]);
    }
}
