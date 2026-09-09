use auslander::algebra::{commutative_square, linear_an, truncated_poly};
use auslander::almost_split::{AlmostSplitOutcome, almost_split, stable_end, stable_hom};
use auslander::ar::tau;
use auslander::hom::hom_dim;
use auslander::indec::IndecomposableModule;
use auslander::module::Module;
use auslander::quiver::ArrowId;

use crate::common::{duality_sequence, duality_witness, f2, f5, preprojective_a3};

use super::support::tier1_fixtures;

#[test]
fn almost_split_runs_on_every_simple_with_a_verifying_duality_witness() {
    for (name, algebra) in tier1_fixtures() {
        let nv = algebra.quiver().num_vertices();
        for v in 0..nv {
            let s = Module::simple(&algebra, v);
            let ind = IndecomposableModule::new(&s).unwrap();
            match almost_split(&ind).unwrap() {
                AlmostSplitOutcome::Projective => {
                    assert!(ind.is_projective(), "{name}: S_{v} projective outcome");
                    assert!(tau(&s).unwrap().is_zero(), "{name}: tau S_{v} is zero");
                }
                AlmostSplitOutcome::Sequence(sequence) => {
                    assert!(!ind.is_projective(), "{name}: S_{v} sequence outcome");
                    let ses = sequence.sequence();
                    assert!(ses.quotient().ptr_eq(&s), "{name}: S_{v} ends its sequence");
                    for w in 0..nv {
                        assert_eq!(
                            ses.middle().dim_at(w),
                            ses.sub().dim_at(w) + ses.quotient().dim_at(w),
                            "{name}: dim tau S_{v} + dim S_{v} = dim middle at vertex {w}"
                        );
                    }
                    let witness = duality_witness(&sequence);
                    assert!(
                        witness.verify(&ind, ses, sequence.chosen_ar_class()),
                        "{name}: duality witness for S_{v}"
                    );
                    // The standalone translate route must agree with the
                    // sub term, matrix for matrix: tau is deterministic.
                    let translate = tau(&s).unwrap();
                    assert!(
                        !translate.is_zero(),
                        "{name}: tau S_{v} is zero for a non-projective simple"
                    );
                    assert_eq!(
                        translate.dim_vector(),
                        ses.sub().dim_vector(),
                        "{name}: tau route dimension for S_{v}"
                    );
                    for a in 0..algebra.quiver().num_arrows() {
                        let arrow = ArrowId(a as u32);
                        assert_eq!(
                            translate.map(arrow).entries_u64(),
                            ses.sub().map(arrow).entries_u64(),
                            "{name}: tau route matrices for S_{v} at arrow {a}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn almost_split_terms_match_the_hand_derived_values() {
    // Commutative square over F_5, by the AR formula derivation of
    // tests/acceptance_nonmonomial.rs row 9: tau S_0 = [1, 1, 1, 0],
    // tau S_1 = [0, 0, 1, 1], tau S_2 = [0, 1, 0, 1], and S_3 = P_3 is
    // projective.
    let square = commutative_square(f5());
    let expected: [&[usize]; 3] = [&[1, 1, 1, 0], &[0, 0, 1, 1], &[0, 1, 0, 1]];
    for (v, sub_dims) in expected.iter().enumerate() {
        let ind = IndecomposableModule::new(&Module::simple(&square, v as u32)).unwrap();
        let sequence = duality_sequence(&ind);
        assert_eq!(
            sequence.sequence().sub().dim_vector(),
            *sub_dims,
            "square: tau S_{v}"
        );
    }
    let p3 = IndecomposableModule::new(&Module::simple(&square, 3)).unwrap();
    assert!(matches!(
        almost_split(&p3).unwrap(),
        AlmostSplitOutcome::Projective
    ));

    // Preprojective A_3 over F_2 is self-injective, so no simple is
    // projective. The translate dimension vectors are the QPA-verified
    // values of tests/acceptance_nonmonomial.rs row 9.
    let b = preprojective_a3();
    let expected: [&[usize]; 3] = [&[0, 1, 1], &[1, 1, 1], &[1, 1, 0]];
    for (v, sub_dims) in expected.iter().enumerate() {
        let ind = IndecomposableModule::new(&Module::simple(&b, v as u32)).unwrap();
        let sequence = duality_sequence(&ind);
        assert_eq!(
            sequence.sequence().sub().dim_vector(),
            *sub_dims,
            "preprojective: tau S_{v}"
        );
    }

    // Linear A_3 over F_5: Hom between interval modules is at most one
    // line, and the hand-derived zigzag AR quiver gives the meshes
    // 0 -> S_1 -> I_1 -> S_0 -> 0 and 0 -> S_2 -> P_1 -> S_1 -> 0.
    let a3 = linear_an(3, f5());
    let s0 = IndecomposableModule::new(&Module::simple(&a3, 0)).unwrap();
    let sequence = duality_sequence(&s0);
    assert_eq!(sequence.sequence().sub().dim_vector(), &[0, 1, 0]);
    assert_eq!(sequence.sequence().middle().dim_vector(), &[1, 1, 0]);
    let s1 = IndecomposableModule::new(&Module::simple(&a3, 1)).unwrap();
    let sequence = duality_sequence(&s1);
    assert_eq!(sequence.sequence().sub().dim_vector(), &[0, 0, 1]);
    assert_eq!(sequence.sequence().middle().dim_vector(), &[0, 1, 1]);
    let s2 = IndecomposableModule::new(&Module::simple(&a3, 2)).unwrap();
    assert!(matches!(
        almost_split(&s2).unwrap(),
        AlmostSplitOutcome::Projective
    ));

    // k[x]/(x^n) is symmetric, so tau S = Omega^2 S = S, and the unique
    // non-split self-extension of S is the uniserial module of dimension
    // 2: the sequence is 0 -> S -> rad P -> S -> 0 over both fields.
    for field in [f2(), f5()] {
        let x3 = truncated_poly(3, field).unwrap();
        let s = IndecomposableModule::new(&Module::simple(&x3, 0)).unwrap();
        let sequence = duality_sequence(&s);
        assert_eq!(sequence.sequence().sub().dim_vector(), &[1]);
        assert_eq!(sequence.sequence().middle().dim_vector(), &[2]);
        assert_eq!(sequence.sequence().quotient().dim_vector(), &[1]);
    }
}

#[test]
fn stable_hom_dimensions_are_consistent_everywhere() {
    for (name, algebra) in tier1_fixtures() {
        let nv = algebra.quiver().num_vertices();
        // The identity of a projective factors through its own cover, so
        // its stable endomorphism space is zero.
        for v in 0..nv {
            let p = Module::projective(&algebra, v);
            assert_eq!(
                stable_end(&p).unwrap().dim(),
                0,
                "{name}: stable End(P_{v})"
            );
        }
        let mut family: Vec<Module> = (0..nv).map(|v| Module::simple(&algebra, v)).collect();
        family.extend((0..nv).map(|v| Module::projective(&algebra, v)));
        for m in &family {
            for target in &family {
                assert!(
                    stable_hom(m, target).unwrap().dim() <= hom_dim(m, target).unwrap(),
                    "{name}: stable Hom({:?}, {:?}) exceeds Hom",
                    m.dim_vector(),
                    target.dim_vector()
                );
            }
        }
    }
}
