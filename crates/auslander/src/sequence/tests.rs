use super::splitting::retraction_system;
use super::*;
use crate::algebra::{an_with_relations, linear_an, truncated_poly};
use crate::ext::{ExtClass, ExtSpace};
use crate::field::PrimeField;
use crate::hom::{Morphism, identity, zero_morphism};
use crate::homspace::scale_morphism;
use crate::module::{Module, direct_sum};

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn one_class(space: &ExtSpace) -> ExtClass {
    let field = space.source().field();
    let mut coords = vec![field.zero(); space.dim()];
    coords[0] = field.one();
    space.class_from_coordinates(&coords).unwrap()
}

#[test]
fn new_accepts_a_direct_sum_and_split_status_verifies() {
    let algebra = linear_an(3, f5());
    let s = Module::simple(&algebra, 0);
    let p = Module::projective(&algebra, 1);
    let (sum, inclusions, projections) = direct_sum(&[&s, &p]);
    let ses = ShortExactSequence::new(inclusions[0].clone(), projections[1].clone()).unwrap();
    assert!(ses.sub().ptr_eq(&s));
    assert!(ses.middle().ptr_eq(&sum));
    assert!(ses.quotient().ptr_eq(&p));
    match ses.split_status() {
        SplitStatus::Split(witness) => {
            assert!(witness.verify(&ses));
            assert!(witness.retraction().source().ptr_eq(&sum));
            assert!(witness.retraction().target().ptr_eq(&s));
            assert!(witness.section().source().ptr_eq(&p));
            assert!(witness.section().target().ptr_eq(&sum));
        }
        SplitStatus::NonSplit(_) => panic!("a direct sum sequence splits"),
    }
}

#[test]
fn new_rejects_each_defect_with_a_typed_error() {
    let algebra = linear_an(3, f5());
    let s = Module::simple(&algebra, 0);
    let p = Module::projective(&algebra, 1);
    let (sum, inclusions, projections) = direct_sum(&[&s, &p]);
    let (_, _, other_projections) = direct_sum(&[&s, &p]);
    assert_eq!(
        ShortExactSequence::new(inclusions[0].clone(), other_projections[1].clone()).unwrap_err(),
        SequenceError::EndpointMismatch
    );
    let zero_inclusion = zero_morphism(&s, &sum).unwrap();
    assert_eq!(
        ShortExactSequence::new(zero_inclusion, projections[1].clone()).unwrap_err(),
        SequenceError::NotMono { vertex: 0 }
    );
    let zero_projection = zero_morphism(&sum, &p).unwrap();
    assert_eq!(
        ShortExactSequence::new(inclusions[0].clone(), zero_projection).unwrap_err(),
        SequenceError::NotEpi { vertex: 1 }
    );
    assert_eq!(
        ShortExactSequence::new(inclusions[0].clone(), projections[0].clone()).unwrap_err(),
        SequenceError::CompositeNonzero { vertex: 0 }
    );
    let (_, triple_inclusions, triple_projections) = direct_sum(&[&s, &p, &s]);
    assert_eq!(
        ShortExactSequence::new(triple_inclusions[0].clone(), triple_projections[1].clone())
            .unwrap_err(),
        SequenceError::DimensionMismatch { vertex: 0 }
    );
}

#[test]
fn from_ext1_of_a_nonzero_class_is_non_split_and_round_trips() {
    for field in [f5(), f2()] {
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let space = ExtSpace::new(&s, &s, 1).unwrap();
        assert_eq!(space.dim(), 1);
        let xi = one_class(&space);
        let ses = ShortExactSequence::from_ext1(&xi).unwrap();
        assert_eq!(ses.sub().dim_vector(), &[1]);
        assert_eq!(ses.middle().dim_vector(), &[2]);
        assert_eq!(ses.quotient().dim_vector(), &[1]);
        let recovered = ses.ext1_class(&space).unwrap();
        assert!(
            recovered.equals(&xi).unwrap(),
            "round trip over F_{}",
            field.modulus()
        );
        match ses.split_status() {
            SplitStatus::NonSplit(witness) => {
                assert!(witness.verify(&ses));
                let mut bad = witness.dual().to_vec();
                bad[0] = field.add(bad[0], field.one());
                assert!(!NonSplitWitness { dual: bad }.verify(&ses));
                let zeros = vec![field.zero(); witness.dual().len()];
                assert!(!NonSplitWitness { dual: zeros }.verify(&ses));
                assert!(!NonSplitWitness { dual: Vec::new() }.verify(&ses));
            }
            SplitStatus::Split(_) => panic!("a nonzero Ext^1 class gives a non-split sequence"),
        }
    }
}

#[test]
fn from_ext1_of_the_zero_class_splits_with_a_verifying_witness() {
    let algebra = truncated_poly(3, f5()).unwrap();
    let s = Module::simple(&algebra, 0);
    let space = ExtSpace::new(&s, &s, 1).unwrap();
    let ses = ShortExactSequence::from_ext1(&space.zero_class()).unwrap();
    assert_eq!(ses.middle().dim_vector(), &[2]);
    match ses.split_status() {
        SplitStatus::Split(witness) => assert!(witness.verify(&ses)),
        SplitStatus::NonSplit(_) => panic!("the zero class gives a split sequence"),
    }
    let recovered = ses.ext1_class(&space).unwrap();
    assert!(recovered.is_zero());
}

#[test]
fn from_ext1_over_a_projective_quotient_uses_the_empty_presentation() {
    // S_2 is projective over linear A_3, so Ext^1(S_2, S_0) = 0 and the
    // resolution of S_2 has no differential.
    let algebra = linear_an(3, f5());
    let s0 = Module::simple(&algebra, 0);
    let s2 = Module::simple(&algebra, 2);
    let space = ExtSpace::new(&s2, &s0, 1).unwrap();
    assert_eq!(space.dim(), 0);
    let ses = ShortExactSequence::from_ext1(&space.zero_class()).unwrap();
    assert_eq!(ses.sub().dim_vector(), &[1, 0, 0]);
    assert_eq!(ses.quotient().dim_vector(), &[0, 0, 1]);
    match ses.split_status() {
        SplitStatus::Split(witness) => assert!(witness.verify(&ses)),
        SplitStatus::NonSplit(_) => panic!("the zero class gives a split sequence"),
    }
    assert!(ses.ext1_class(&space).unwrap().is_zero());
}

// Over kA_3/(ab) the extension of S_0 by S_1 with class the Ext^1
// generator is P_0 (dimension vector (1, 1, 0)), and the extension of
// S_1 by S_2 is P_1 (dimension vector (0, 1, 1)); both are non-split.
// Splicing them realizes the Yoneda product, which is the Ext^2
// generator detected by the relation: the product of the recovered
// classes is nonzero in the one-dimensional Ext^2(S_0, S_2).
#[test]
fn round_trip_and_splicing_agreement_over_a3_mod_ab() {
    let field = f5();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let s0 = Module::simple(&algebra, 0);
    let s1 = Module::simple(&algebra, 1);
    let s2 = Module::simple(&algebra, 2);
    let space_a = ExtSpace::new(&s0, &s1, 1).unwrap();
    let space_b = ExtSpace::new(&s1, &s2, 1).unwrap();
    let alpha = one_class(&space_a);
    let beta = one_class(&space_b);
    let ses_a = ShortExactSequence::from_ext1(&alpha).unwrap();
    let ses_b = ShortExactSequence::from_ext1(&beta).unwrap();
    assert_eq!(ses_a.middle().dim_vector(), &[1, 1, 0]);
    assert_eq!(ses_b.middle().dim_vector(), &[0, 1, 1]);
    let recovered_a = ses_a.ext1_class(&space_a).unwrap();
    let recovered_b = ses_b.ext1_class(&space_b).unwrap();
    assert!(recovered_a.equals(&alpha).unwrap());
    assert!(recovered_b.equals(&beta).unwrap());
    for ses in [&ses_a, &ses_b] {
        match ses.split_status() {
            SplitStatus::NonSplit(witness) => assert!(witness.verify(ses)),
            SplitStatus::Split(_) => panic!("the generator classes are non-split"),
        }
    }
    let spliced = recovered_a.then(&recovered_b).unwrap();
    let direct = alpha.then(&beta).unwrap();
    assert_eq!(spliced.space().dim(), 1);
    assert!(
        !spliced.is_zero(),
        "the spliced 2-extension class is nonzero"
    );
    assert!(spliced.equals(&direct).unwrap());
}

#[test]
fn split_witness_rejects_a_tampered_retraction_or_section() {
    let algebra = linear_an(3, f5());
    let field = f5();
    let s = Module::simple(&algebra, 0);
    let p = Module::projective(&algebra, 1);
    let (_, inclusions, projections) = direct_sum(&[&s, &p]);
    let ses = ShortExactSequence::new(inclusions[0].clone(), projections[1].clone()).unwrap();
    let SplitStatus::Split(witness) = ses.split_status() else {
        panic!("a direct sum sequence splits");
    };
    let scale = |f: &Morphism| scale_morphism(f, field.elem(2));
    let bad_retraction = SplitWitness {
        retraction: scale(witness.retraction()),
        section: witness.section().clone(),
    };
    assert!(!bad_retraction.verify(&ses));
    let bad_section = SplitWitness {
        retraction: witness.retraction().clone(),
        section: scale(witness.section()),
    };
    assert!(!bad_section.verify(&ses));
}

// Section 15 of the design: a dual vector with y A != 0, and a dual
// vector with y b = 0. Adding a unit vector at a nonzero row of A
// moves y A off zero; the zero vector and the doubled vector keep
// y A = 0 and fail y b = 1.
#[test]
fn a_tampered_or_zero_dual_vector_fails_verification() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let space = ExtSpace::new(&s, &s, 1).unwrap();
    let ses = ShortExactSequence::from_ext1(&one_class(&space)).unwrap();
    let SplitStatus::NonSplit(witness) = ses.split_status() else {
        panic!("the generator class does not split");
    };
    assert!(witness.verify(&ses));
    let (a, _) = retraction_system(&ses);
    let r = (0..a.rows())
        .find(|&r| a.row(r).iter().any(|v| !v.is_zero()))
        .expect("the retraction system has a nonzero row");
    let mut dual = witness.dual().to_vec();
    dual[r] = field.add(dual[r], field.one());
    let off_kernel = NonSplitWitness { dual };
    assert!(!off_kernel.verify(&ses), "y A is nonzero");
    let zero = NonSplitWitness {
        dual: vec![field.zero(); witness.dual().len()],
    };
    assert!(!zero.verify(&ses), "y b is zero");
    let doubled = NonSplitWitness {
        dual: witness
            .dual()
            .iter()
            .map(|&y| field.mul(field.elem(2), y))
            .collect(),
    };
    assert!(!doubled.verify(&ses), "y b is two");
}

#[test]
fn ext1_class_rejects_a_space_with_wrong_degree_or_endpoints() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let space = ExtSpace::new(&s, &s, 1).unwrap();
    let ses = ShortExactSequence::from_ext1(&one_class(&space)).unwrap();
    let deg2 = ExtSpace::new(&s, &s, 2).unwrap();
    assert_eq!(
        ses.ext1_class(&deg2).unwrap_err(),
        SequenceError::WrongDegree {
            expected: 1,
            got: 2
        }
    );
    let s_copy = Module::simple(&algebra, 0);
    let wrong_source = ExtSpace::new(&s_copy, &s, 1).unwrap();
    assert_eq!(
        ses.ext1_class(&wrong_source).unwrap_err(),
        SequenceError::SpaceSourceMismatch
    );
    let wrong_target = ExtSpace::new(&s, &s_copy, 1).unwrap();
    assert_eq!(
        ses.ext1_class(&wrong_target).unwrap_err(),
        SequenceError::SpaceTargetMismatch
    );
}

#[test]
fn from_ext1_rejects_a_class_of_the_wrong_degree() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let deg0 = ExtSpace::new(&s, &s, 0).unwrap().identity_class().unwrap();
    assert_eq!(
        ShortExactSequence::from_ext1(&deg0).unwrap_err(),
        SequenceError::WrongDegree {
            expected: 1,
            got: 0
        }
    );
    let deg2 = one_class(&ExtSpace::new(&s, &s, 2).unwrap());
    assert_eq!(
        ShortExactSequence::from_ext1(&deg2).unwrap_err(),
        SequenceError::WrongDegree {
            expected: 1,
            got: 2
        }
    );
}

#[test]
fn a_zero_sub_gives_an_isomorphism_like_split_sequence() {
    let algebra = linear_an(3, f5());
    let p = Module::projective(&algebra, 0);
    let z = Module::zero(&algebra);
    let inclusion = zero_morphism(&z, &p).unwrap();
    let ses = ShortExactSequence::new(inclusion, identity(&p)).unwrap();
    match ses.split_status() {
        SplitStatus::Split(witness) => assert!(witness.verify(&ses)),
        SplitStatus::NonSplit(_) => panic!("a zero-sub sequence splits"),
    }
}

#[test]
fn from_ext1_and_split_status_are_deterministic_across_recomputation() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let space = ExtSpace::new(&s, &s, 1).unwrap();
    let xi = one_class(&space);
    let first = ShortExactSequence::from_ext1(&xi).unwrap();
    let second = ShortExactSequence::from_ext1(&xi).unwrap();
    for v in 0..algebra.quiver().num_vertices() {
        assert_eq!(
            first.inclusion().map_at(v).entries_u64(),
            second.inclusion().map_at(v).entries_u64()
        );
        assert_eq!(
            first.projection().map_at(v).entries_u64(),
            second.projection().map_at(v).entries_u64()
        );
    }
    let (SplitStatus::NonSplit(a), SplitStatus::NonSplit(b)) =
        (first.split_status(), second.split_status())
    else {
        panic!("the generator class is non-split");
    };
    assert_eq!(
        a.dual().iter().map(|c| c.raw()).collect::<Vec<_>>(),
        b.dual().iter().map(|c| c.raw()).collect::<Vec<_>>()
    );
}

// The one-pass route saves an elimination on a non-split sequence and must
// return exactly what the two-pass route returns, on both outcomes.
#[test]
fn the_one_pass_split_status_agrees_with_the_two_pass_one() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let p = Module::projective(&algebra, 0);
    let (_, inclusions, projections) = direct_sum(&[&s, &p]);
    let split = ShortExactSequence::new(inclusions[0].clone(), projections[1].clone()).unwrap();
    let space = ExtSpace::new(&s, &s, 1).unwrap();
    let nonsplit = ShortExactSequence::from_ext1(&one_class(&space)).unwrap();
    for sequence in [&split, &nonsplit] {
        match (sequence.split_status(), sequence.split_status_one_pass()) {
            (SplitStatus::Split(a), SplitStatus::Split(b)) => {
                assert_eq!(a.retraction(), b.retraction());
                assert_eq!(a.section(), b.section());
                assert!(b.verify(sequence));
            }
            (SplitStatus::NonSplit(a), SplitStatus::NonSplit(b)) => {
                assert_eq!(a.dual(), b.dual());
                assert!(b.verify(sequence));
            }
            _ => panic!("the two routes disagree on the outcome"),
        }
    }
}
