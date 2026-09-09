use crate::algebra::{commutative_square, linear_an, truncated_poly};
use crate::arquiver::IndecomposableCatalog;
use crate::homspace::HomSpace;
use crate::module::Module;
use crate::radical::radical;

use super::super::{AlmostSplitOutcome, projectively_trivial, stable_end};
use super::support::*;

// A = k[x]/(x^3) is symmetric, so tau = Omega^2. Omega S = ker(P -> S) =
// rad P, of dimension 2. The cover of rad P is P again (top rad P = S),
// with kernel soc P = S, so Omega^2 S = S and tau S = S. The minimal
// resolution of S is period-2 with every term P and Hom(P, S) = k with
// zero differentials, so Ext^1(S, S) has dimension 1. End(S) = k, and
// the one map S -> P lands in soc P, so its composite with P ->> S is
// zero: stable End(S) has dimension 1 = Ext dimension, the radical of
// End(S) is zero, and the socle is the whole Ext space, of dimension 1 =
// residue degree. The chosen class is the generator, and its extension
// is the unique non-split self-extension of S: the uniserial module of
// dimension 2. The sequence is 0 -> S -> rad P -> S -> 0.
#[test]
fn truncated_poly_3_simple_has_the_uniserial_almost_split_sequence() {
    for field in [f5(), f2()] {
        let algebra = truncated_poly(3, field).unwrap();
        let s = indec(&Module::simple(&algebra, 0));
        let sequence = sequence_of(&s);
        assert_eq!(sequence.sequence().sub().dim_vector(), &[1]);
        assert_eq!(sequence.sequence().middle().dim_vector(), &[2]);
        assert_eq!(sequence.sequence().quotient().dim_vector(), &[1]);
        assert_eq!(
            middle_classes(sequence.sequence().middle()),
            vec![(vec![2], 1)]
        );
        let witness = duality_witness(&sequence);
        assert_eq!(witness.ext_dim(), 1);
        assert_eq!(witness.stable_end_dim(), 1);
        assert_eq!(witness.socle_dim(), 1);
        assert_eq!(witness.residue_degree(), 1);
        assert_eq!(witness.chosen_row(), 0);
        assert!(witness.action_traces().is_empty(), "rad End(S) = 0");
        assert!(witness.verify(&s, sequence.sequence(), sequence.chosen_ar_class()));
    }
}

// R = rad P over k[x]/(x^3) is (x) = A/(x^2), of dimension 2. The cover
// P -> R (1 |-> x) has kernel ann(x) = (x^2) = S, so Omega R = S and
// tau R = Omega^2 R = Omega S = rad P = R. End(R) = A/(x^2) has
// dimension 2 with radical spanned by multiplication by x. Hom(R, P) =
// ann(x^2) = span{x, x^2} has dimension 2, and composing with P ->> R
// kills x^2 and keeps x, so the projectively trivial part of End(R) has
// dimension 1 and stable End(R) has dimension 1 = Ext^1(R, tau R). The
// socle then has dimension 1 = residue degree, and the sequence of the
// chosen class is the unique non-split extension class up to scalar. One
// such sequence is explicit: 0 -> A/(x^2) -> A/(x) (+) A/(x^3) ->
// A/(x^2) -> 0 with a |-> (a mod x, x a) and (b, c) |-> x b - c; it is
// exact by the dimension count 2 = 1 + 3 - 2 and non-split because
// S (+) P has no summand of dimension 2. So the middle is S (+) P with
// dimension vectors [1] and [3].
#[test]
fn truncated_poly_3_rad_p_has_middle_simple_plus_projective() {
    for field in [f5(), f2()] {
        let algebra = truncated_poly(3, field).unwrap();
        let p = Module::projective(&algebra, 0);
        let r = indec(&radical(&p).0);
        let sequence = sequence_of(&r);
        assert_eq!(sequence.sequence().sub().dim_vector(), &[2]);
        assert_eq!(sequence.sequence().middle().dim_vector(), &[4]);
        assert_eq!(sequence.sequence().quotient().dim_vector(), &[2]);
        assert_eq!(
            middle_classes(sequence.sequence().middle()),
            vec![(vec![1], 1), (vec![3], 1)]
        );
        let witness = duality_witness(&sequence);
        assert_eq!(witness.ext_dim(), 1);
        assert_eq!(witness.stable_end_dim(), 1);
        assert_eq!(witness.socle_dim(), 1);
        assert_eq!(
            witness.action_traces().len(),
            1,
            "rad End(R) has dimension 1"
        );
        assert!(
            witness
                .action_traces()
                .iter()
                .all(|trace| trace.iter().all(|v| v.is_zero()))
        );
        assert!(witness.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
    }
}

// Right modules over linear A_3 with arrows a: 0 -> 1, b: 1 -> 2.
// P_1 = e_1 A has basis {e_1, b} with top S_1 and rad P_1 = S_2, so
// 0 -> S_2 -> P_1 -> S_1 -> 0 is exact and non-split. tau S_1 = S_2 (the
// tau tests of ar.rs pin the dimension vector (0, 0, 1)), and
// Ext^1(S_1, S_2) = k: one dimension per arrow 1 -> 2. End(S_1) = k,
// and Hom(S_1, P_1) = 0 because A-linearity at b forces the vertex-1
// component to vanish against the isomorphism P_1(b), so stable
// End(S_1) = k and the socle is the whole Ext space. The chosen class
// is the generator, whose middle is the non-split extension P_1.
#[test]
fn linear_a3_sequence_ending_at_s1_has_middle_p1() {
    let algebra = linear_an(3, f5());
    let s1 = indec(&Module::simple(&algebra, 1));
    let sequence = sequence_of(&s1);
    assert_eq!(sequence.sequence().sub().dim_vector(), &[0, 0, 1]);
    assert_eq!(sequence.sequence().middle().dim_vector(), &[0, 1, 1]);
    assert_eq!(sequence.sequence().quotient().dim_vector(), &[0, 1, 0]);
    assert_eq!(
        middle_classes(sequence.sequence().middle()),
        vec![(vec![0, 1, 1], 1)]
    );
    let witness = duality_witness(&sequence);
    assert_eq!(witness.socle_dim(), 1);
    assert_eq!(witness.residue_degree(), 1);
    assert!(witness.verify(&s1, sequence.sequence(), sequence.chosen_ar_class()));
}

// I_1 over linear A_3 has dimension vector (1, 1, 0), top S_0, and
// cover P_0 with kernel P_2, so its presentation is P_2 -> P_0 -> I_1.
// tau I_1 = ker(nu(d_1): I_2 -> I_0) has dimension 3 - 1 + dim nu(I_1)
// = 2 by exactness, because Hom(I_1, A) = 0 (any component into a
// projective dies against the isomorphisms P_i(b) or the zero spaces),
// so tau I_1 = (0, 1, 1) = P_1. Zigzag through the meshes: the mesh
// 0 -> S_2 -> P_1 -> S_1 -> 0 gives the irreducible map P_1 -> S_1, and
// rad P_0 = P_1 gives the irreducible inclusion P_1 -> P_0. These are
// the two arrows out of tau I_1 = P_1, so the middle of the mesh ending
// at I_1 is S_1 (+) P_0, of dimension vector (1, 2, 1): the D4-free
// mesh 0 -> P_1 -> S_1 (+) P_0 -> I_1 -> 0.
#[test]
fn linear_a3_sequence_ending_at_i1_matches_the_mesh() {
    let algebra = linear_an(3, f5());
    let i1 = indec(&Module::injective(&algebra, 1));
    assert_eq!(i1.module().dim_vector(), &[1, 1, 0]);
    let sequence = sequence_of(&i1);
    assert_eq!(sequence.sequence().sub().dim_vector(), &[0, 1, 1]);
    assert_eq!(sequence.sequence().middle().dim_vector(), &[1, 2, 1]);
    assert_eq!(
        middle_classes(sequence.sequence().middle()),
        vec![(vec![0, 1, 0], 1), (vec![1, 1, 1], 1)]
    );
    let witness = duality_witness(&sequence);
    assert_eq!(witness.socle_dim(), 1);
    assert!(witness.verify(&i1, sequence.sequence(), sequence.chosen_ar_class()));
}

// S_1 over the commutative square is not projective: P_1 has dimension
// vector (0, 1, 0, 1). tau comes from the crate's double-route tau; the
// test pins the checkable invariants instead of a full hand value: the
// sequence is exact with dim tau + dim S_1 = dim E, non-split with a
// verifying witness, and End(S_1) = k forces a one-dimensional socle.
#[test]
fn commutative_square_s1_sequence_invariants_hold() {
    let algebra = commutative_square(f5());
    let s1 = indec(&Module::simple(&algebra, 1));
    let sequence = sequence_of(&s1);
    assert_eq!(sequence.sequence().quotient().dim_vector(), &[0, 1, 0, 0]);
    assert_eq!(
        sequence.sequence().sub().total_dim() + sequence.sequence().quotient().total_dim(),
        sequence.sequence().middle().total_dim()
    );
    let witness = duality_witness(&sequence);
    assert_eq!(witness.ext_dim(), witness.stable_end_dim());
    assert_eq!(witness.socle_dim(), 1);
    assert_eq!(witness.residue_degree(), 1);
    assert!(witness.verify(&s1, sequence.sequence(), sequence.chosen_ar_class()));
}

// The preprojective algebra of A_3 over F_2 is self-injective, so no
// simple is projective and every simple has an almost-split sequence.
// The hand derivation of tau S_0 is not pinned; the test pins the
// checkable invariants: the dimension count, a passing witness, and the
// one-dimensional socle forced by End(S_0) = k.
#[test]
fn preprojective_a3_simple_sequence_invariants_hold() {
    let algebra = preprojective_a3();
    let s0 = indec(&Module::simple(&algebra, 0));
    assert!(!s0.is_projective());
    let sequence = sequence_of(&s0);
    assert_eq!(
        sequence.sequence().sub().total_dim() + sequence.sequence().quotient().total_dim(),
        sequence.sequence().middle().total_dim()
    );
    let witness = duality_witness(&sequence);
    assert_eq!(witness.ext_dim(), witness.stable_end_dim());
    assert_eq!(witness.socle_dim(), 1);
    assert_eq!(witness.residue_degree(), 1);
    assert!(witness.verify(&s0, sequence.sequence(), sequence.chosen_ar_class()));
}

// Over A = k[x]/(x^4) let M = A/(x^2) = rad^2 P, of dimension 2.
// Omega M = (x^2), which is isomorphic to A/ann(x^2) = A/(x^2) = M, so
// tau M = Omega^2 M = M for this symmetric algebra. The minimal
// resolution repeats A -x^2-> A, and Hom(A, tau M) = tau M has dimension
// 2 with zero induced differentials because x^2 kills A/(x^2), so
// Ext^1(M, tau M) has dimension 2. End(M) = A/(x^2) has dimension 2;
// Hom(M, A) = ann(x^2) = span{x^2, x^3}, and both composites with
// A ->> M are zero, so stable End(M) has dimension 2 as well. The
// radical of End(M) is spanned by x, so the socle gate forces dimension
// 1 = residue degree: a proper socle inside a two-dimensional Ext space.
// The right map of the mesh 0 -> A/(x^2) ->
// A/(x) (+) A/(x^3) -> A/(x^2) -> 0, (b, c) |-> x b - c, is right
// almost split: a non-retraction A/(x^i) -> M either lands in rad M and
// factors through the A/(x) leg (h = x u factors as x b with b the mod-x
// reduction of u), or is epi with i >= 3 and factors through the
// A/(x^3) leg. So the middle is A/(x) (+) A/(x^3), dimensions 1 and 3.
#[test]
fn truncated_poly_4_interval_module_has_a_proper_socle() {
    let field = f5();
    let algebra = truncated_poly(4, field).unwrap();
    let p = Module::projective(&algebra, 0);
    let m = indec(&radical(&radical(&p).0).0);
    assert_eq!(m.module().dim_vector(), &[2]);
    let sequence = sequence_of(&m);
    assert_eq!(sequence.sequence().sub().dim_vector(), &[2]);
    assert_eq!(sequence.sequence().middle().dim_vector(), &[4]);
    assert_eq!(
        middle_classes(sequence.sequence().middle()),
        vec![(vec![1], 1), (vec![3], 1)]
    );
    let witness = duality_witness(&sequence);
    assert_eq!(witness.ext_dim(), 2);
    assert_eq!(witness.stable_end_dim(), 2);
    assert_eq!(witness.socle_dim(), 1);
    assert_eq!(witness.residue_degree(), 1);
    assert_eq!(witness.action_traces().len(), 1);
    assert_eq!(witness.action_traces()[0].len(), 2);
    assert!(witness.action_traces()[0].iter().all(|v| v.is_zero()));
    assert!(witness.verify(&m, sequence.sequence(), sequence.chosen_ar_class()));
}

// S_2 = P_2 over linear A_3 is projective, so its identity factors
// through the cover and stable End(S_2) = 0. S_1 is not projective and
// Hom(S_1, P_1) = 0, so stable End(S_1) = End(S_1) = k. Over k[x]/(x^3)
// the space Hom(rad P, rad P) = End(A/(x^2)) has dimension 2; the
// projectively trivial part is the image of Hom(rad P, P) =
// span{x, x^2} under composition with P ->> rad P, which kills x^2 and
// keeps x: dimension 1, so stable End(rad P) has dimension 1.
#[test]
fn stable_hom_dimensions_match_hand_counts() {
    let a3 = linear_an(3, f5());
    let s2 = Module::simple(&a3, 2);
    assert_eq!(stable_end(&s2).unwrap().dim(), 0);
    let s1 = Module::simple(&a3, 1);
    assert_eq!(stable_end(&s1).unwrap().dim(), 1);
    for field in [f5(), f2()] {
        let algebra = truncated_poly(3, field).unwrap();
        let p = Module::projective(&algebra, 0);
        let r = radical(&p).0;
        let space = HomSpace::new(&r, &r).unwrap();
        assert_eq!(space.dim(), 2);
        assert_eq!(projectively_trivial(&space).unwrap().dim(), 1);
        assert_eq!(stable_end(&r).unwrap().dim(), 1);
    }
}

#[test]
fn projective_inputs_return_the_projective_outcome() {
    let a3 = linear_an(3, f5());
    for v in 0..3 {
        let p = indec(&Module::projective(&a3, v));
        assert!(matches!(
            super::super::almost_split(&p).unwrap(),
            AlmostSplitOutcome::Projective
        ));
    }
    let algebra = truncated_poly(3, f2()).unwrap();
    let p = indec(&Module::projective(&algebra, 0));
    assert!(matches!(
        super::super::almost_split(&p).unwrap(),
        AlmostSplitOutcome::Projective
    ));
    let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
    assert!(matches!(
        super::super::almost_split_via_catalog(&p, &catalog).unwrap(),
        AlmostSplitOutcome::Projective
    ));
}
