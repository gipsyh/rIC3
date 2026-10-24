mod ops;
mod option;

#[cfg(bitwuzla_stub)]
mod stub;
#[cfg(bitwuzla_stub)]
pub use stub::Bitwuzla;

#[cfg(not(bitwuzla_stub))]
mod ffi;
#[cfg(not(bitwuzla_stub))]
pub use ffi::Bitwuzla;

#[cfg(all(test, not(bitwuzla_stub)))]
mod tests {
    use super::*;
    use giputils::bitvec::BitVec;
    use logicrs::fol::{FolOp, Sort, Term};

    #[test]
    fn test0() {
        let mut bzla = Bitwuzla::new();
        let a = Term::new_var(Sort::Bv(2));
        let b = Term::new_var(Sort::Bv(2));
        let a_add_b = a.op1(FolOp::Add, &b);
        let b_add_a = b.op1(FolOp::Add, &a);
        bzla.assert(&a_add_b.op1(FolOp::Neq, &b_add_a));
        assert!(!bzla.solve([]));
    }

    #[test]
    fn test1() {
        let mut bzla = Bitwuzla::new();
        let bv2c2 = BitVec::from_usize(2, 2);
        let t_bv2c2 = Term::bv_const(bv2c2.clone());
        let a = Term::new_var(Sort::Bv(2));
        let b = Term::new_var(Sort::Bv(2));
        let a_eq_2 = a.op1(FolOp::Eq, &t_bv2c2);
        let a_eq_b = a.op1(FolOp::Eq, &b);
        assert!(bzla.solve(&[a_eq_2, a_eq_b]));
        assert!(bzla.sat_value(&a).unwrap().eq(&bv2c2));
        assert!(bzla.sat_value(&b).unwrap().eq(&bv2c2));
    }

    #[test]
    fn test2() {
        let mut bzla = Bitwuzla::new();
        let bv1c1 = BitVec::from_usize(1, 1);
        let t_bv1c1 = Term::bv_const(bv1c1);
        bzla.assert(&t_bv1c1);
    }

    #[test]
    fn concat() {
        let mut bzla = Bitwuzla::new();
        let bv2c3 = BitVec::from_usize(2, 3);
        let t_bv2c3 = Term::bv_const(bv2c3);
        let bv3c0 = BitVec::from_usize(3, 0);
        let t_bv3c0 = Term::bv_const(bv3c0);
        let bv5c3 = BitVec::from_usize(5, 3);
        let t_bv5c3 = Term::bv_const(bv5c3);
        let tneq = t_bv5c3.tneq(&t_bv3c0.concat(&t_bv2c3));
        assert!(!bzla.solve(&[tneq]));
    }

    #[test]
    fn slice() {
        let mut bzla = Bitwuzla::new();
        let a = Term::new_var(Sort::Bv(4));
        let slice = a.slice(1, 3);
        let c14 = Term::bv_const(BitVec::from_usize(4, 14));
        bzla.assert(&a.teq(&c14));
        assert!(bzla.solve([]));
        let val = bzla.sat_value(&slice);
        assert_eq!(val.unwrap(), BitVec::from_usize(3, 7));
    }

    #[test]
    fn unsat_assumps_only_returns_conflicting_assumptions() {
        let mut bzla = Bitwuzla::new();
        let x = Term::new_var(Sort::Bv(2));
        let y = Term::new_var(Sort::Bv(2));
        let x_eq_0 = x.teq(Term::bv_const(BitVec::from_usize(2, 0)));
        let x_eq_1 = x.teq(Term::bv_const(BitVec::from_usize(2, 1)));
        let y_eq_0 = y.teq(Term::bv_const(BitVec::from_usize(2, 0)));

        assert!(!bzla.solve([&x_eq_0, &x_eq_1, &y_eq_0]));

        let unsat_assumptions = bzla.unsat_assump();
        assert_eq!(unsat_assumptions.len(), 2);
        assert!(unsat_assumptions.contains(&x_eq_0));
        assert!(unsat_assumptions.contains(&x_eq_1));
        assert!(!unsat_assumptions.contains(&y_eq_0));
    }

    #[test]
    fn unsat_core_includes_assertions_and_assumptions() {
        let mut bzla = Bitwuzla::new();
        let x = Term::new_var(Sort::Bv(2));
        let y = Term::new_var(Sort::Bv(2));
        let x_eq_0 = x.teq(Term::bv_const(BitVec::from_usize(2, 0)));
        let x_eq_1 = x.teq(Term::bv_const(BitVec::from_usize(2, 1)));
        let y_eq_0 = y.teq(Term::bv_const(BitVec::from_usize(2, 0)));

        bzla.assert(&x_eq_0);
        assert!(!bzla.solve([&x_eq_1, &y_eq_0]));

        let unsat_core = bzla.unsat_core();
        assert_eq!(unsat_core.len(), 2);
        assert!(unsat_core.contains(&x_eq_0));
        assert!(unsat_core.contains(&x_eq_1));
        assert!(!unsat_core.contains(&y_eq_0));

        let unsat_assumptions = bzla.unsat_assump();
        assert_eq!(unsat_assumptions, vec![x_eq_1]);
    }
}

#[cfg(all(test, bitwuzla_stub))]
#[test]
#[should_panic(expected = "Bitwuzla library not found")]
fn missing_library_reports_how_to_install_bitwuzla() {
    Bitwuzla::new();
}
