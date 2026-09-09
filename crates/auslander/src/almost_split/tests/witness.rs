use crate::algebra::truncated_poly;
use crate::arquiver::IndecomposableCatalog;
use crate::ext::ExtSpace;
use crate::field::Fp;
use crate::hom::hom;
use crate::homspace::{row_times, scale_morphism};
use crate::linalg::{DenseMat, RowReducer};
use crate::module::{Module, direct_sum};
use crate::radical::radical;
use crate::sequence::{ShortExactSequence, SplitStatus};

use super::super::stable::{action_matrices, action_matrix};
use super::super::{ArDualityWitness, DefectKind};
use super::support::*;

#[test]
fn a_tampered_action_trace_fails_verification() {
    let algebra = truncated_poly(3, f5()).unwrap();
    let p = Module::projective(&algebra, 0);
    let r = indec(&radical(&p).0);
    let sequence = sequence_of(&r);
    let mut bad = duality_witness(&sequence).clone();
    assert_eq!(bad.action_traces.len(), 1);
    bad.action_traces[0][0] = f5().one();
    assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
}

#[test]
fn a_swapped_socle_row_fails_verification() {
    let field = f5();
    let algebra = truncated_poly(4, field).unwrap();
    let p = Module::projective(&algebra, 0);
    let m = indec(&radical(&radical(&p).0).0);
    let sequence = sequence_of(&m);
    let witness = duality_witness(&sequence);
    let socle = witness.socle_rref().clone();
    let dim = witness.ext_dim();
    let mut reducer = RowReducer::new(dim);
    for r in 0..socle.rows() {
        reducer.push(socle.row(r), &field);
    }
    let candidate = (0..dim)
        .map(|k| {
            let mut row = vec![field.zero(); dim];
            row[k] = field.one();
            row
        })
        // A rejected row already lies in the socle span, so the push that
        // rejects it leaves the reducer alone.
        .find(|row| reducer.push(row, &field))
        .expect("the socle is proper, so some unit vector lies outside it");
    let action = action_matrices(&m, sequence.chosen_ar_class().space()).unwrap();
    assert!(
        action.iter().any(|a| row_times(&candidate, a, &field)
            .iter()
            .any(|v| !v.is_zero())),
        "the replacement vector is not annihilated, so it is not in the socle"
    );
    let mut bad = witness.clone();
    bad.socle_rref = DenseMat::from_rows(&[candidate]);
    assert!(!bad.verify(&m, sequence.sequence(), sequence.chosen_ar_class()));
}

// The dual vectors of the S sequence and the rad P sequence over
// k[x]/(x^3) certify retraction systems of different sizes. Grafting
// one into the other's witness is a tamper the dual-vector recheck
// rejects.
#[test]
fn a_tampered_dual_vector_fails_verification() {
    let algebra = truncated_poly(3, f5()).unwrap();
    let s = indec(&Module::simple(&algebra, 0));
    let p = Module::projective(&algebra, 0);
    let r = indec(&radical(&p).0);
    let s_sequence = sequence_of(&s);
    let r_sequence = sequence_of(&r);
    let s_witness = duality_witness(&s_sequence);
    let r_witness = duality_witness(&r_sequence);
    assert_ne!(
        s_witness.non_split().dual().len(),
        r_witness.non_split().dual().len()
    );
    let mut bad = s_witness.clone();
    bad.non_split = r_witness.non_split().clone();
    assert!(!bad.verify(&s, s_sequence.sequence(), s_sequence.chosen_ar_class()));
}

// A witness grafted onto an Ext space whose target is not tau M: every
// stored matrix and dimension matches the recomputation over the wrong
// space (rad End(S) = 0 on both sides), and the grafted non-split
// witness certifies the wrong sequence, so only the translate gate can
// reject.
#[test]
fn a_space_with_the_wrong_target_fails_duality_verification() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = indec(&Module::simple(&algebra, 0));
    let genuine = sequence_of(&s);
    let witness = duality_witness(&genuine);
    let r = radical(&Module::projective(&algebra, 0)).0;
    let wrong_space = ExtSpace::new(s.module(), &r, 1).unwrap();
    assert_eq!(wrong_space.dim(), 1);
    let class = wrong_space.class_from_coordinates(&[field.one()]).unwrap();
    let sequence = ShortExactSequence::from_ext1(&class).unwrap();
    let SplitStatus::NonSplit(non_split) = sequence.split_status() else {
        panic!("the nonzero class does not split");
    };
    let mut bad = witness.clone();
    bad.non_split = non_split;
    assert!(!bad.verify(&s, &sequence, &class));
}

#[test]
fn a_dimension_field_altered_in_either_direction_fails_verification() {
    let algebra = truncated_poly(3, f5()).unwrap();
    let p = Module::projective(&algebra, 0);
    let r = indec(&radical(&p).0);
    let sequence = sequence_of(&r);
    let witness = duality_witness(&sequence);
    assert!(witness.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
    for delta in [1isize, -1] {
        let shift = |v: usize| (v as isize + delta) as usize;
        let mut bad = witness.clone();
        bad.ext_dim = shift(bad.ext_dim);
        assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
        let mut bad = witness.clone();
        bad.stable_end_dim = shift(bad.stable_end_dim);
        assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
        let mut bad = witness.clone();
        bad.socle_dim = shift(bad.socle_dim);
        assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
        let mut bad = witness.clone();
        bad.residue_degree = shift(bad.residue_degree);
        assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
    }
}

// Defect values are not constructible through the public API; only
// their Display texts are pinned.
#[test]
fn defect_kind_display_is_stable() {
    assert_eq!(
        DefectKind::DualityDimensionMismatch {
            ext_dim: 2,
            stable_end_dim: 1
        }
        .to_string(),
        "Ext^1(M, tau M) has dimension 2, stable End(M) has dimension 1; crate defect"
    );
    assert_eq!(
        DefectKind::SocleDimensionMismatch {
            socle_dim: 0,
            residue_degree: 1
        }
        .to_string(),
        "the Ext socle has dimension 0, the residue degree is 1; crate defect"
    );
    assert_eq!(
        DefectKind::ProjectivityDisagreement {
            resolution_projective: true,
            tau_zero: false
        }
        .to_string(),
        "the resolution route reports projective = true, tau reports zero = false; \
         crate defect"
    );
    assert_eq!(
        DefectKind::NonzeroClassSplit.to_string(),
        "the sequence of a nonzero chosen class splits; crate defect"
    );
    assert_eq!(
        DefectKind::RightFactorizationMismatch { entry: 3 }.to_string(),
        "the image of Hom(X, E) in Hom(X, M) differs from rad(X, M) at catalog entry 3; \
         crate defect"
    );
    assert_eq!(
        DefectKind::LeftFactorizationMismatch { entry: 0 }.to_string(),
        "the image of Hom(E, X) in Hom(tau M, X) differs from rad(tau M, X) at catalog \
         entry 0; crate defect"
    );
}

// The first fixture with residue degree above 1. Every shipped fixture
// before it has residue degree 1, so its socle is a line and the socle
// gate is one-dimensional. Here the residue field is F_8, so the socle is
// a 3-dimensional proper subspace of a 6-dimensional Ext space.
#[test]
fn the_quasi_length_two_module_has_a_three_dimensional_socle_in_a_six_dimensional_ext_space() {
    let w = indec(&quasi_length_two_in_the_f8_tube());
    assert_eq!(w.endo().dim(), 6);
    assert_eq!(w.endo().radical_dim(), 3);
    assert_eq!(w.residue_degree(), 3);
    let sequence = sequence_of(&w);
    let witness = duality_witness(&sequence);
    assert_eq!(witness.ext_dim(), 6);
    assert_eq!(witness.stable_end_dim(), 6);
    assert_eq!(witness.socle_dim(), 3);
    assert_eq!(sequence.chosen_ar_class().space().dim(), 6);
    assert_eq!(witness.chosen_row(), 0);
    assert!(sequence.verify(&w));
    // tau fixes every regular Kronecker module, and the middle term of a
    // mesh in a homogeneous tube is the module twice.
    assert_eq!(sequence.sequence().sub().dim_vector(), &[6, 6]);
    assert_eq!(sequence.sequence().middle().dim_vector(), &[12, 12]);
}

// Section 15 of the design, at residue degree above 1: a witness built
// from socle row 1 carries that row's own valid non-split witness and
// annihilates every action matrix, so the sequence it names is almost
// split. It is not the crate's chosen class, whose coordinates the
// fresh-process fingerprint pins, so verify rejects the row index.
#[test]
fn a_chosen_row_other_than_zero_fails_duality_verification() {
    let w = indec(&quasi_length_two_in_the_f8_tube());
    let sequence = sequence_of(&w);
    let witness = duality_witness(&sequence);
    let space = sequence.chosen_ar_class().space();
    let socle = witness.socle_rref();
    assert!(socle.rows() >= 2, "the socle has a row other than 0");
    let field = w.module().field();
    let other = space.class_from_coordinates(socle.row(1)).unwrap();
    let action = action_matrices(&w, space).unwrap();
    let traces: Vec<Vec<Fp>> = action
        .iter()
        .map(|a| row_times(other.coordinates(), a, &field))
        .collect();
    assert!(
        traces.iter().flatten().all(|v| v.is_zero()),
        "socle row 1 annihilates rad End(M)"
    );
    let other_sequence = ShortExactSequence::from_ext1(&other).unwrap();
    let SplitStatus::NonSplit(non_split) = other_sequence.split_status() else {
        panic!("a nonzero socle class gives a non-split sequence");
    };
    assert!(non_split.verify(&other_sequence));
    let row_one = ArDualityWitness {
        radical_coords: witness.radical_basis_coords().clone(),
        action_traces: traces,
        socle_rref: socle.clone(),
        chosen_row: 1,
        ext_dim: witness.ext_dim(),
        stable_end_dim: witness.stable_end_dim(),
        socle_dim: witness.socle_dim(),
        residue_degree: witness.residue_degree(),
        non_split,
    };
    assert!(!row_one.verify(&w, &other_sequence, &other));
}

// Section 15 of the design: the Ext space a witness certifies against is
// untrusted data like any other. Here `B^1` has no rows, so replacing it
// with the complement row leaves every gate intact: the action list is
// empty, the socle stays the whole line, and `class_from_cocycle` still
// returns [1] because the complement column pivots first. Only the recheck
// of the space against a fresh computation rejects it.
#[test]
fn a_coboundary_basis_forged_from_the_complement_fails_duality_verification() {
    let s = simple_over_truncated_poly_3();
    let sequence = sequence_of(&s);
    let witness = duality_witness(&sequence);
    let class = sequence.chosen_ar_class();
    assert!(witness.verify(&s, sequence.sequence(), class));
    let space = class.space();
    assert_eq!(space.coboundary_basis().rows(), 0);
    assert_eq!(space.complement_basis().rows(), 1);
    let forged = space.with_bases(
        space.cocycle_basis().clone(),
        space.complement_basis().clone(),
        space.complement_basis().clone(),
    );
    let bad = forged.class_from_coordinates(class.coordinates()).unwrap();
    assert_eq!(bad.coordinates(), class.coordinates());
    assert!(!witness.verify(&s, sequence.sequence(), &bad));
}

// Section 15 of the design: nothing outside the space recheck ever reads
// the stored cocycle basis, so an emptied `Z^1` passes every other gate.
#[test]
fn an_emptied_cocycle_basis_fails_duality_verification() {
    let s = simple_over_truncated_poly_3();
    let sequence = sequence_of(&s);
    let witness = duality_witness(&sequence);
    let class = sequence.chosen_ar_class();
    let space = class.space();
    let width = space.cocycle_basis().cols();
    let forged = space.with_bases(
        DenseMat::zero(0, width),
        space.coboundary_basis().clone(),
        space.complement_basis().clone(),
    );
    let bad = forged.class_from_coordinates(class.coordinates()).unwrap();
    assert!(!witness.verify(&s, sequence.sequence(), &bad));
}

// Section 15 of the design: `reps` is a cache of the complement, and with
// `rad End(S) = 0` there is no action matrix to disturb, so a scaled
// representative changes no other stored value. The space recheck is what
// rejects it.
#[test]
fn a_scaled_representative_fails_duality_verification() {
    let s = simple_over_truncated_poly_3();
    let sequence = sequence_of(&s);
    let witness = duality_witness(&sequence);
    let class = sequence.chosen_ar_class();
    let space = class.space();
    assert_eq!(witness.radical_basis_coords().rows(), 0);
    let scaled = space
        .representatives()
        .iter()
        .map(|rep| scale_morphism(rep, f5().elem(2)))
        .collect();
    let forged = space.with_representatives(scaled);
    let bad = forged.class_from_coordinates(class.coordinates()).unwrap();
    assert!(!witness.verify(&s, sequence.sequence(), &bad));
}

// The action is a left one: Ext^1(-, N) is contravariant, so the matrix
// assignment reverses the crate's diagrammatic product. Nothing computed
// depends on the side, because rad End(M) is two-sided, but the docs used
// to name the wrong side and this pins the real identity.
#[test]
fn the_action_matrices_reverse_composition() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    // End(S (+) S) is the full 2 x 2 matrix algebra, so the basis has
    // pairs that do not commute.
    let (m, _, _) = direct_sum(&[&s, &s]);
    let space = ExtSpace::new(&m, &s, 1).unwrap();
    assert_eq!(space.dim(), 2);
    let end = hom(&m, &m).unwrap();
    let mut saw_noncommuting = false;
    for phi in &end {
        for psi in &end {
            let a_phi = action_matrix(&space, phi).unwrap();
            let a_psi = action_matrix(&space, psi).unwrap();
            let composite = action_matrix(&space, &phi.then(psi).unwrap()).unwrap();
            assert_eq!(composite, a_psi.mul(&a_phi, &field));
            if a_psi.mul(&a_phi, &field) != a_phi.mul(&a_psi, &field) {
                saw_noncommuting = true;
            }
        }
    }
    assert!(
        saw_noncommuting,
        "the fixture exercises a noncommutative End"
    );
}

// The two verify entry points feed the sequence and class the value
// holds, and each rejects the other route's witness.
#[test]
fn the_sequence_verifies_through_its_own_witness_and_rejects_the_other_route() {
    let algebra = truncated_poly(3, f5()).unwrap();
    let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
    let s = indec(&Module::simple(&algebra, 0));
    let duality = sequence_of(&s);
    assert!(duality.verify(&s));
    assert!(!duality.verify_with_catalog(&s, &catalog));
    let through_catalog = catalog_sequence_of(&s, &catalog);
    assert!(through_catalog.verify_with_catalog(&s, &catalog));
    assert!(!through_catalog.verify(&s));
}
