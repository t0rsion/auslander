//! v0.4 mutation corpus for the AR layer (design section 15).
//!
//! Every mutation reachable from the public API is exercised below. Several
//! section 15 bullets target stored witness fields that no public
//! constructor can set. Those mutations are built field by field in the
//! in-module unit tests of src/ext.rs, src/sequence.rs, src/almost_split.rs,
//! and src/arquiver.rs; this file drives the nearest public route to the
//! same verify branch. The bullets and their in-module tests:
//!
//! - "a complement row replaced by a coboundary" and "a product reduced
//!   against a tampered coboundary basis": ext.rs
//!   `a_complement_row_replaced_by_a_coboundary_fails_product_verification`
//!   and `a_tampered_coboundary_basis_fails_product_verification`.
//! - "a lift family violating one lift identity": ext.rs
//!   `product_witness_accepts_the_genuine_triple_and_rejects_tampering`
//!   scales one stored lift. The public route below feeds `verify` a
//!   rescaled factor, which fails the same identity.
//! - "a split witness whose retraction fails the identity by one entry":
//!   sequence.rs `split_witness_rejects_a_tampered_retraction_or_section`.
//! - "a dual vector with y A != 0" and "a dual vector with y b = 0":
//!   sequence.rs `a_tampered_or_zero_dual_vector_fails_verification`.
//! - "an action trace claiming e . r = 0 falsely" and "a socle RREF
//!   containing a non-socle row": almost_split.rs
//!   `a_tampered_action_trace_fails_verification` and
//!   `a_swapped_socle_row_fails_verification`.
//! - "dimension equalities off by one in each DefectKind direction":
//!   almost_split.rs
//!   `a_dimension_field_altered_in_either_direction_fails_verification`.
//! - "a catalog witness missing one factorization": almost_split.rs
//!   `a_tampered_catalog_factorization_coordinate_fails_verification`
//!   drops a stored factorization vector.
//! - "a valued arrow with a non-dividing residue degree": arquiver.rs
//!   `valued_arrow_arithmetic_and_the_division_gate_are_pinned` calls the
//!   division routine directly; the same gate runs inside `ar_quiver`.

use auslander::algebra::commutative_square;
use auslander::algebra::{linear_an, truncated_poly};
use auslander::almost_split::{
    AlmostSplitOutcome, AlmostSplitSequence, AlmostSplitWitness, ArDualityWitness, CatalogWitness,
    almost_split, almost_split_via_catalog,
};
use auslander::arquiver::IndecomposableCatalog;
use auslander::dynkin::DynkinError;
use auslander::enumerate::EnumerateError;
use auslander::ext::{ExtClass, ExtClassError, ExtSpace};
use auslander::field::PrimeField;
use auslander::hom::{HomError, Morphism, hom, zero_morphism};
use auslander::indec::IndecomposableModule;
use auslander::linalg::DenseMat;
use auslander::module::{Module, direct_sum};
use auslander::radical::radical;
use auslander::sequence::{SequenceError, ShortExactSequence, SplitStatus};

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn basis_class(space: &ExtSpace, k: usize) -> ExtClass {
    let field = space.source().field();
    let mut coords = vec![field.zero(); space.dim()];
    coords[k] = field.one();
    space.class_from_coordinates(&coords).unwrap()
}

/// Every entry of `f` multiplied by `c`.
fn scale_morphism(f: &Morphism, c: auslander::field::Fp) -> Morphism {
    let field = f.source().field();
    let nv = f.source().algebra().quiver().num_vertices();
    let maps = (0..nv)
        .map(|v| {
            let m = f.map_at(v);
            let mut out = DenseMat::zero(m.rows(), m.cols());
            for r in 0..m.rows() {
                for (col, &entry) in m.row(r).iter().enumerate() {
                    out.set(r, col, field.mul(c, entry));
                }
            }
            out
        })
        .collect();
    Morphism::new(f.source(), f.target(), maps).unwrap()
}

fn duality_sequence(m: &IndecomposableModule) -> AlmostSplitSequence {
    match almost_split(m).unwrap() {
        AlmostSplitOutcome::Sequence(sequence) => sequence,
        AlmostSplitOutcome::Projective => panic!("expected a sequence, got Projective"),
    }
}

fn catalog_sequence(
    m: &IndecomposableModule,
    catalog: &IndecomposableCatalog,
) -> AlmostSplitSequence {
    match almost_split_via_catalog(m, catalog).unwrap() {
        AlmostSplitOutcome::Sequence(sequence) => sequence,
        AlmostSplitOutcome::Projective => panic!("expected a sequence, got Projective"),
    }
}

fn duality_witness(sequence: &AlmostSplitSequence) -> &ArDualityWitness {
    match sequence.witness() {
        AlmostSplitWitness::ArDuality(witness) => witness,
        AlmostSplitWitness::ExhaustiveCatalog(_) => panic!("expected the AR duality witness"),
    }
}

fn catalog_witness(sequence: &AlmostSplitSequence) -> &CatalogWitness {
    match sequence.witness() {
        AlmostSplitWitness::ExhaustiveCatalog(witness) => witness,
        AlmostSplitWitness::ArDuality(_) => panic!("expected the catalog witness"),
    }
}

// Section 15: a non-exact sequence at one vertex, assembled from a wrong
// projection or inclusion. Over linear A_3 with S = S_0 and P = P_1 the
// sum S + P has dimension vector (1, 1, 1).
#[test]
fn the_sequence_constructor_rejects_each_non_exact_assembly() {
    let algebra = linear_an(3, f5());
    let s = Module::simple(&algebra, 0);
    let p = Module::projective(&algebra, 1);
    let (sum, inclusions, projections) = direct_sum(&[&s, &p]);
    // the projection onto the sub summand: the composite is the identity
    // of S, nonzero at vertex 0
    assert_eq!(
        ShortExactSequence::new(inclusions[0].clone(), projections[0].clone()).unwrap_err(),
        SequenceError::CompositeNonzero { vertex: 0 }
    );
    // a middle term with one extra S summand: sub plus quotient misses the
    // middle dimension at vertex 0
    let (_, triple_inclusions, triple_projections) = direct_sum(&[&s, &p, &s]);
    assert_eq!(
        ShortExactSequence::new(triple_inclusions[0].clone(), triple_projections[1].clone())
            .unwrap_err(),
        SequenceError::DimensionMismatch { vertex: 0 }
    );
    // the zero map is no inclusion of a nonzero sub: rank 0 < 1 at vertex 0
    assert_eq!(
        ShortExactSequence::new(zero_morphism(&s, &sum).unwrap(), projections[1].clone())
            .unwrap_err(),
        SequenceError::NotMono { vertex: 0 }
    );
    // the zero map is no projection onto a nonzero quotient: P_1 first has
    // dimension at vertex 1
    assert_eq!(
        ShortExactSequence::new(inclusions[0].clone(), zero_morphism(&sum, &p).unwrap())
            .unwrap_err(),
        SequenceError::NotEpi { vertex: 1 }
    );
    // a projection out of a separately built middle: not pointer-equal
    let (_, _, other_projections) = direct_sum(&[&s, &p]);
    assert_eq!(
        ShortExactSequence::new(inclusions[0].clone(), other_projections[1].clone()).unwrap_err(),
        SequenceError::EndpointMismatch
    );
}

// Section 15: a tampered inclusion that is not a morphism. Scaling only
// the vertex 1 block of the sum inclusion P_0 -> P_0 + S_2 breaks the
// commuting square at the arrow a: 0 -> 1, because f_0 * Sum(a) keeps the
// old value while P_0(a) * f_1 doubles. The morphism gate rejects the
// maps, so the tampered sequence cannot even be assembled.
#[test]
fn a_tampered_inclusion_fails_the_morphism_square() {
    let field = f5();
    let algebra = linear_an(3, field);
    let p0 = Module::projective(&algebra, 0);
    let s2 = Module::simple(&algebra, 2);
    let (sum, inclusions, _) = direct_sum(&[&p0, &s2]);
    let genuine = &inclusions[0];
    let nv = algebra.quiver().num_vertices();
    let mut maps: Vec<DenseMat> = (0..nv).map(|v| genuine.map_at(v).clone()).collect();
    let scaled = scale_morphism(genuine, field.elem(2));
    maps[1] = scaled.map_at(1).clone();
    match Morphism::new(&p0, &sum, maps) {
        Err(HomError::SquareViolated { .. }) => {}
        other => panic!("expected SquareViolated, got {other:?}"),
    }
}

// Section 15: a cochain failing d.then(f) = 0 into class_from_cocycle.
// Over A = k[x]/(x^3) the cochain space Hom(P_1, P) has dimension 3, and
// delta^1 composes with d_2 = right multiplication by x^2, so a basis
// element sending the generator to a unit is no cocycle. P is injective
// over this self-injective algebra, so Ext^1(S, P) = 0 and every cocycle
// here has the zero class.
#[test]
fn class_from_cocycle_rejects_a_non_cocycle_and_carries_the_composite() {
    let algebra = truncated_poly(3, f5()).unwrap();
    let s = Module::simple(&algebra, 0);
    let p = Module::projective(&algebra, 0);
    let space = ExtSpace::new(&s, &p, 1).unwrap();
    assert_eq!(space.dim(), 0);
    let cochains = hom(space.cochain_term(), space.target()).unwrap();
    assert_eq!(cochains.len(), 3);
    let mut rejected = 0usize;
    for f in &cochains {
        match space.class_from_cocycle(f) {
            Ok(class) => assert!(class.is_zero()),
            Err(ExtClassError::NotCocycle { composite }) => {
                assert!(
                    composite.iter().any(|c| !c.is_zero()),
                    "the error carries the nonzero composite"
                );
                rejected += 1;
            }
            Err(other) => panic!("expected NotCocycle, got {other:?}"),
        }
    }
    assert!(rejected > 0, "Hom(P_1, P) contains non-cocycles");
}

// Section 15: coordinates of the wrong length, plus an entry from the
// wrong field.
#[test]
fn class_from_coordinates_rejects_wrong_lengths_and_non_canonical_entries() {
    let algebra = truncated_poly(3, f2()).unwrap();
    let s = Module::simple(&algebra, 0);
    let space = ExtSpace::new(&s, &s, 1).unwrap();
    assert_eq!(space.dim(), 1);
    assert_eq!(
        space.class_from_coordinates(&[]).unwrap_err(),
        ExtClassError::CoordinateCountMismatch {
            expected: 1,
            got: 0
        }
    );
    let one = f2().one();
    assert_eq!(
        space.class_from_coordinates(&[one, one]).unwrap_err(),
        ExtClassError::CoordinateCountMismatch {
            expected: 1,
            got: 2
        }
    );
    // 3 is a canonical F_5 element and no canonical F_2 element
    assert_eq!(
        space.class_from_coordinates(&[f5().elem(3)]).unwrap_err(),
        ExtClassError::NonCanonicalCoordinate { index: 0 }
    );
}

// Section 15: a lift family violating one lift identity, and a tampered
// product class in the right space with wrong coordinates. ProductWitness
// has no public constructor, so a directly mutated lift vector is
// unconstructible here; rescaling a factor fails the identity
// phi_0.then(aug) = representative against the stored lifts, which drives
// the same verify branch. src/ext.rs rebuilds the lift family in-crate.
// Over k[x]/(x^3) the Ext algebra of S is k[z] tensor the exterior
// algebra on y, so the product of the degree 1 and degree 2 generators is
// nonzero in the one-dimensional Ext^3(S, S).
#[test]
fn a_product_witness_rejects_a_wrong_class_and_rescaled_factors() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let ext1 = ExtSpace::new(&s, &s, 1).unwrap();
    let ext2 = ExtSpace::new(&s, &s, 2).unwrap();
    let alpha = basis_class(&ext1, 0);
    let beta = basis_class(&ext2, 0);
    let (product, witness) = alpha.then_with_witness(&beta).unwrap();
    assert!(!product.is_zero());
    assert!(witness.verify(&alpha, &beta, &product));
    let mut wrong_coords = product.coordinates().to_vec();
    wrong_coords[0] = field.add(wrong_coords[0], field.one());
    let wrong = product
        .space()
        .class_from_coordinates(&wrong_coords)
        .unwrap();
    assert!(!witness.verify(&alpha, &beta, &wrong));
    let two = field.elem(2);
    assert!(!witness.verify(&alpha.scale(two), &beta, &product));
    assert!(!witness.verify(&alpha, &beta.scale(two), &product));
}

// Section 15: a split witness whose retraction fails the identity.
// SplitWitness has no public constructor, so the corpus takes the witness
// of a genuinely different split sequence: doubling the inclusion keeps
// the sequence exact but changes the retraction it certifies, and against
// the original sequence iota.then(r') = (1/2) id != id. src/sequence.rs
// rescales the stored fields in-crate.
#[test]
fn a_split_witness_from_a_rescaled_sequence_fails_against_the_original() {
    let field = f5();
    let algebra = linear_an(3, field);
    let s = Module::simple(&algebra, 0);
    let p = Module::projective(&algebra, 1);
    let (sum, inclusions, projections) = direct_sum(&[&s, &p]);
    let original = ShortExactSequence::new(inclusions[0].clone(), projections[1].clone()).unwrap();
    let doubled = scale_morphism(&inclusions[0], field.elem(2));
    assert!(doubled.source().ptr_eq(&s) && doubled.target().ptr_eq(&sum));
    let rescaled = ShortExactSequence::new(doubled, projections[1].clone()).unwrap();
    let SplitStatus::Split(genuine) = original.split_status() else {
        panic!("a direct sum sequence splits");
    };
    assert!(genuine.verify(&original));
    let SplitStatus::Split(foreign) = rescaled.split_status() else {
        panic!("a rescaled direct sum sequence splits");
    };
    assert!(foreign.verify(&rescaled));
    assert!(!foreign.verify(&original));
}

// Section 15: a dual vector with y A != 0, and one with y b = 0.
// NonSplitWitness has no public constructor, so a hand-built dual vector
// is unconstructible here; src/sequence.rs mutates the stored vector
// entry by entry. The public mutation grafts a genuine dual vector onto
// the split sequence of the zero class. Both sequences share the shapes
// [1], [2], [1], so both retraction systems have two commuting square
// rows and one identity row, and the split system is solvable: no vector
// at all passes y A = 0 with y b = 1, so verify must reject.
#[test]
fn a_dual_vector_does_not_certify_a_solvable_retraction_system() {
    let algebra = truncated_poly(3, f5()).unwrap();
    let s = Module::simple(&algebra, 0);
    let space = ExtSpace::new(&s, &s, 1).unwrap();
    let xi = basis_class(&space, 0);
    let nonsplit = ShortExactSequence::from_ext1(&xi).unwrap();
    let split = ShortExactSequence::from_ext1(&space.zero_class()).unwrap();
    assert_eq!(nonsplit.middle().dim_vector(), split.middle().dim_vector());
    let SplitStatus::NonSplit(witness) = nonsplit.split_status() else {
        panic!("a nonzero class does not split");
    };
    assert!(witness.verify(&nonsplit));
    assert_eq!(witness.dual().len(), 3);
    assert!(!witness.verify(&split));
    // from_ext1 is deterministic, so the witness still certifies a
    // recomputed copy of its own sequence
    let recomputed = ShortExactSequence::from_ext1(&basis_class(&space, 0)).unwrap();
    assert!(witness.verify(&recomputed));
}

// Section 15: a tampered action trace and a tampered socle row target
// stored fields with no public constructor; src/almost_split.rs rebuilds
// them in-crate. The public mutations below drive the same verify checks:
// a class whose coordinates differ from the stored socle row, a module
// whose endpoints differ, and a sequence with foreign endpoints. R =
// rad P over k[x]/(x^3) has rad End(R) of dimension 1, so the witness
// stores one action trace and the trace recheck runs.
#[test]
fn an_ar_duality_witness_rejects_a_wrong_class_module_or_sequence() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let r = IndecomposableModule::new(&radical(&Module::projective(&algebra, 0)).0).unwrap();
    let s = IndecomposableModule::new(&Module::simple(&algebra, 0)).unwrap();
    let r_sequence = duality_sequence(&r);
    let s_sequence = duality_sequence(&s);
    let witness = duality_witness(&r_sequence);
    assert_eq!(witness.action_traces().len(), 1);
    assert!(witness.verify(&r, r_sequence.sequence(), r_sequence.chosen_ar_class()));
    let wrong_class = r_sequence.chosen_ar_class().scale(field.elem(2));
    assert!(!wrong_class.is_zero());
    assert!(!witness.verify(&r, r_sequence.sequence(), &wrong_class));
    assert!(!witness.verify(&s, r_sequence.sequence(), r_sequence.chosen_ar_class()));
    assert!(!witness.verify(&r, s_sequence.sequence(), r_sequence.chosen_ar_class()));
}

// Section 15: a catalog witness missing one factorization targets a
// stored field with no public constructor; src/almost_split.rs tampers
// the stored coordinates in-crate. The public mutations below exercise
// the catalog identity, class, and sequence gates of verify.
#[test]
fn a_catalog_witness_rejects_a_foreign_catalog_class_or_sequence() {
    let field = f2();
    let algebra = truncated_poly(3, field).unwrap();
    let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
    let s = IndecomposableModule::new(&Module::simple(&algebra, 0)).unwrap();
    let sequence = catalog_sequence(&s, &catalog);
    let witness = catalog_witness(&sequence);
    assert!(witness.verify(
        &s,
        &catalog,
        sequence.sequence(),
        sequence.chosen_ar_class()
    ));
    // a catalog over a separately built copy of the same algebra: the
    // same mathematics, a different Arc, rejected by pointer discipline
    let rebuilt = truncated_poly(3, field).unwrap();
    let foreign = IndecomposableCatalog::nakayama(&rebuilt).unwrap();
    assert!(!witness.verify(
        &s,
        &foreign,
        sequence.sequence(),
        sequence.chosen_ar_class()
    ));
    // doubling the class gives zero over F_2, and the zero class is never
    // almost split
    let doubled = sequence
        .chosen_ar_class()
        .add(sequence.chosen_ar_class())
        .unwrap();
    assert!(doubled.is_zero());
    assert!(!witness.verify(&s, &catalog, sequence.sequence(), &doubled));
    // the sequence of another catalog vertex has foreign endpoints
    let r = &catalog.entries()[1];
    assert_eq!(r.module().dim_vector(), &[2]);
    let r_sequence = catalog_sequence(r, &catalog);
    assert!(!witness.verify(
        &s,
        &catalog,
        r_sequence.sequence(),
        sequence.chosen_ar_class()
    ));
}

// Section 15: forged catalog provenance. IndecomposableCatalog has no
// public constructor from module lists: the only constructors are
// nakayama and dynkin, each wrapping a complete enumeration, so a
// hand-built module list can never claim completeness. A compile-fail
// assertion is out of scope; the two constructors reject wrong-shaped
// algebras instead.
#[test]
fn catalog_provenance_cannot_be_forged_and_wrong_shapes_are_rejected() {
    // k[x]/(x^3) carries the relation x^3, so Gabriel's theorem does not
    // apply
    let x3 = truncated_poly(3, f5()).unwrap();
    assert_eq!(
        IndecomposableCatalog::dynkin(&x3).unwrap_err(),
        DynkinError::NonzeroIdeal { relations: 1 }
    );
    // the commutative square has two arrows out of vertex 0, so it is not
    // Nakayama
    let square = commutative_square(f5());
    assert_eq!(
        IndecomposableCatalog::nakayama(&square).unwrap_err(),
        EnumerateError::NotNakayama {
            vertex: 0,
            incoming: 0,
            outgoing: 2,
        }
    );
}
