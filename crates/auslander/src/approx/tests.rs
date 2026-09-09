use super::certify::certify;
use super::linear::{radical_coordinates, row_relations, unit_factorizations};
use super::*;
use crate::algebra::{Algebra, commutative_square, kronecker, linear_an, truncated_poly};
use crate::decompose::{add_morphisms, direct_sum_or_zero};
use crate::dynkin::{DynkinType, dynkin_quiver};
use crate::endo::EndoAlgebra;
use crate::field::Fp;
use crate::field::PrimeField;
use crate::hom::{HomError, Morphism, kernel, zero_morphism};
use crate::homspace::HomSpace;
use crate::indec::{IndecError, IndecomposableModule};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::module::direct_sum;
use crate::quiver::Quiver;
use std::sync::Arc;

fn slot_sum(
    source: &Module,
    summands: &[IndecomposableModule],
    slots: &[usize],
) -> (Module, Vec<Morphism>, Vec<Morphism>) {
    direct_sum_or_zero(
        source.algebra(),
        slots.iter().map(|&i| summands[i].module()),
    )
}

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn fields() -> [PrimeField; 2] {
    [f2(), f5()]
}

fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    crate::algebra::path_algebra(quiver, field)
        .expect("the zero ideal over an acyclic quiver completes")
}

fn d4(field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
        field,
    )
}

fn fixtures(field: PrimeField) -> Vec<(&'static str, Arc<Algebra>)> {
    vec![
        ("A_2", linear_an(2, field)),
        ("A_3", linear_an(3, field)),
        ("k[x]/x^3", truncated_poly(3, field).unwrap()),
        ("D_4", d4(field)),
        ("commutative square", commutative_square(field)),
    ]
}

fn projectives(algebra: &Arc<Algebra>) -> Vec<Module> {
    (0..algebra.quiver().num_vertices())
        .map(|v| Module::projective(algebra, v))
        .collect()
}

fn injectives(algebra: &Arc<Algebra>) -> Vec<Module> {
    (0..algebra.quiver().num_vertices())
        .map(|v| Module::injective(algebra, v))
        .collect()
}

fn test_modules(algebra: &Arc<Algebra>) -> Vec<Module> {
    let mut out: Vec<Module> = (0..algebra.quiver().num_vertices())
        .map(|v| Module::simple(algebra, v))
        .collect();
    out.extend(projectives(algebra));
    out.extend(injectives(algebra));
    out
}

// The approximation property, re-solved from scratch rather than read off
// the witness. Every basis map of Hom(X, N_i) is f.then(h) for some h.
fn left_property_holds(a: &MinimalLeftApproximation) -> bool {
    let x = a.map().source();
    let b = a.map().target();
    let field = x.field();
    for n in a.summands() {
        let target_space = HomSpace::new(x, n.module()).unwrap();
        let source_space = HomSpace::new(b, n.module()).unwrap();
        let images: Vec<Vec<Fp>> = source_space
            .basis()
            .iter()
            .map(|h| target_space.coords(&a.map().then(h).unwrap()).unwrap())
            .collect();
        let system = if images.is_empty() {
            DenseMat::zero(target_space.dim(), 0)
        } else {
            DenseMat::from_rows(&images).transpose()
        };
        if unit_factorizations(&system, &field).is_err() {
            return false;
        }
    }
    true
}

// Factorization coordinates for a map that is known to approximate, in the
// layout MinimalLeftApproximation stores.
fn left_factorizations(f: &Morphism, summands: &[IndecomposableModule]) -> Vec<Vec<Vec<Fp>>> {
    let field = f.source().field();
    summands
        .iter()
        .map(|n| {
            let target_space = HomSpace::new(f.source(), n.module()).unwrap();
            let source_space = HomSpace::new(f.target(), n.module()).unwrap();
            let images: Vec<Vec<Fp>> = source_space
                .basis()
                .iter()
                .map(|h| target_space.coords(&f.then(h).unwrap()).unwrap())
                .collect();
            let system = if images.is_empty() {
                DenseMat::zero(target_space.dim(), 0)
            } else {
                DenseMat::from_rows(&images).transpose()
            };
            unit_factorizations(&system, &field).expect("the map approximates")
        })
        .collect()
}

// K_f of a left approximation, recomputed outside the witness.
fn left_kernel_of(f: &Morphism, endo: &EndoAlgebra) -> DenseMat {
    let space = HomSpace::new(f.source(), f.target()).unwrap();
    let field = f.source().field();
    let rows: Vec<Vec<Fp>> = endo
        .basis()
        .iter()
        .map(|e| space.coords(&f.then(e).unwrap()).unwrap())
        .collect();
    row_relations(&rows, space.dim(), &field)
}

#[test]
fn left_approximations_by_the_projectives_verify_on_every_fixture() {
    let mut checked = 0;
    for field in fields() {
        for (name, algebra) in fixtures(field) {
            let generators = projectives(&algebra);
            for x in test_modules(&algebra) {
                let context = format!("{name} over F_{}", field.modulus());
                let left = left_approximation(&x, &generators)
                    .unwrap_or_else(|e| panic!("{context}: left: {e}"));
                assert!(left.verify(), "{context}: left verify");
                assert!(left_property_holds(&left), "{context}: left property");
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 84);
}

#[test]
fn left_approximations_by_the_injectives_verify_on_every_fixture() {
    for field in fields() {
        for (name, algebra) in fixtures(field) {
            let generators = injectives(&algebra);
            for x in test_modules(&algebra) {
                let context = format!("{name} over F_{}", field.modulus());
                let left = left_approximation(&x, &generators)
                    .unwrap_or_else(|e| panic!("{context}: left: {e}"));
                assert!(left.verify(), "{context}: left verify");
                assert!(left_property_holds(&left), "{context}: left property");
            }
        }
    }
}

#[test]
fn every_kernel_row_sits_inside_the_radical_of_the_endomorphism_algebra() {
    for field in fields() {
        for (name, algebra) in fixtures(field) {
            let generators = projectives(&algebra);
            for x in test_modules(&algebra) {
                let left = left_approximation(&x, &generators).unwrap();
                let endo = EndoAlgebra::new(left.map().target());
                let kernel = left_kernel_of(left.map(), &endo);
                assert_eq!(&kernel, left.kernel_basis(), "{name}: recomputed K_f");
                for r in 0..kernel.rows() {
                    assert!(
                        endo.in_radical(kernel.row(r)),
                        "{name} over F_{}: row {r} outside rad End(B)",
                        field.modulus()
                    );
                }
            }
        }
    }
}

// Over linearly oriented A_2 (0 -> a -> 1), P_0 has dimension vector (1, 1)
// and P_1 = S_1 has (0, 1). A map f: S_0 -> P_0 has f_1 = 0 and must satisfy
// f_0 . P_0(a) = S_0(a) . f_1 = 0 with P_0(a) invertible, so f_0 = 0. A map
// S_0 -> P_1 is zero at vertex 0 for lack of room. So Hom(S_0, P_v) = 0 for
// both v, and the minimal left approximation of S_0 by add(P) is the zero
// map into the zero module.
#[test]
fn a_left_approximation_with_no_maps_available_is_the_zero_map_into_zero() {
    for field in fields() {
        let algebra = linear_an(2, field);
        let s0 = Module::simple(&algebra, 0);
        let generators = projectives(&algebra);
        for n in &generators {
            assert_eq!(HomSpace::new(&s0, n).unwrap().dim(), 0);
        }
        let a = left_approximation(&s0, &generators).unwrap();
        assert!(a.slots().is_empty());
        assert!(a.map().target().is_zero());
        assert!(a.map().is_zero());
        assert_eq!(a.kernel_basis().rows(), 0);
        assert!(a.verify());
        assert!(left_property_holds(&a));
    }
}

// X in add(N) gives a split monomorphism. Over A_2 take X = S_1 = P_1.
// Hom(S_1, P_1) = End(S_1) is one-dimensional; Hom(P_0, P_1) = 0, so the
// radical part R_1 is zero and the identity is the single generator. The
// approximation is X -> X, an isomorphism, which is split mono.
//
// Hom(S_1, P_0) is one-dimensional too, the socle inclusion, but every map
// there is the composite S_1 -> P_1 -> P_0 with P_1 and P_0 not isomorphic,
// so R_0 is all of Hom(S_1, P_0) and P_0 gets no copy. That is the part of
// the count an F_p basis would get wrong.
#[test]
fn a_module_inside_add_n_gets_a_split_monomorphism() {
    for field in fields() {
        let algebra = linear_an(2, field);
        let generators = projectives(&algebra);
        let x = generators[1].clone();
        assert_eq!(HomSpace::new(&x, &generators[0]).unwrap().dim(), 1);
        let a = left_approximation(&x, &generators).unwrap();
        assert_eq!(a.multiplicity(0), 0, "P_0 is redundant here");
        assert_eq!(a.slots(), &[1]);
        assert!(a.map().is_isomorphism());
        assert_eq!(kernel(a.map()).0.total_dim(), 0);

        // The factorization payload by value. B is one copy of P_1 and f
        // is the block inclusion of the generator, which is the identity
        // of End(P_1) = k. Hom(X, N_i) and Hom(B, N_i) are both
        // one-dimensional for each i, and f identifies the two, so every
        // basis map factors with the single coordinate 1.
        for (i, n) in generators.iter().enumerate() {
            assert_eq!(HomSpace::new(&x, n).unwrap().dim(), 1);
            assert_eq!(HomSpace::new(a.map().target(), n).unwrap().dim(), 1);
            assert_eq!(a.factorization(i, 0), &[field.one()], "summand {i}");
        }

        assert!(a.verify());
        assert!(left_property_holds(&a));
    }
}

#[test]
fn an_empty_add_generator_list_gives_the_zero_map_into_zero() {
    for field in fields() {
        for (name, algebra) in fixtures(field) {
            let x = Module::projective(&algebra, 0);
            let left = left_approximation(&x, &[]).unwrap();
            assert!(left.summands().is_empty(), "{name}");
            assert!(left.slots().is_empty(), "{name}");
            assert!(left.map().target().is_zero(), "{name}");
            assert!(left.verify(), "{name}");
        }
    }
}

// Over k[x]/x^3 the only indecomposable projective is the regular module P
// of dimension 3, and the algebra is self-injective, so P is also the
// injective envelope of every module. For M = k[x]/x^2,
// Hom(M, P) = {p in P : x^2 p = 0} = span{x, x^2} has F_p dimension 2, and
// Hom(M, P) . rad End(P) = span{x, x^2} . span{x, x^2} = span{x^2} has
// dimension 1. The top is one-dimensional over the residue field
// D = End(P)/rad End(P) = F_p, so the minimal left approximation uses one
// copy of P: the injective envelope M -> P. The naive F_p count would take
// two copies.
#[test]
fn a_truncated_polynomial_module_needs_one_copy_where_the_fp_count_says_two() {
    for field in fields() {
        let algebra = truncated_poly(3, field).unwrap();
        let p = Module::projective(&algebra, 0);
        let mut action = DenseMat::zero(2, 2);
        action.set(0, 1, field.one());
        let m = Module::new(algebra.clone(), vec![2], vec![action]).unwrap();
        assert_eq!(HomSpace::new(&m, &p).unwrap().dim(), 2);

        let a = left_approximation(&m, std::slice::from_ref(&p)).unwrap();
        assert_eq!(a.slots(), &[0], "one copy of P, not two");
        assert_eq!(a.map().target().dim_vector(), &[3]);
        assert_eq!(
            kernel(a.map()).0.total_dim(),
            0,
            "the envelope is injective"
        );

        // The minimality payload by value. f is mono, so
        // K_f = {h in End(P) : f.then(h) = 0} is the set of h vanishing on
        // the image span{x, x^2}, which is multiplication by x^2 alone: a
        // line. rad End(P) is span{x, x^2}, of dimension 2. The kernel row
        // is the first radical basis row, so its coordinates over that
        // basis are (1, 0).
        let endo = EndoAlgebra::new(a.map().target());
        assert_eq!(endo.dim(), 3);
        assert_eq!(endo.radical_dim(), 2);
        assert_eq!(a.kernel_basis().rows(), 1);
        assert_eq!(a.kernel_basis().row(0), endo.radical_basis().row(0));
        assert_eq!(a.radical_coordinates(0), &[field.one(), Fp::ZERO]);

        assert!(a.verify());
        assert!(left_property_holds(&a));
    }
}

// The Kronecker representation (I_3, C) over F_2 with C the companion
// matrix of x^3 + x + 1, irreducible over F_2, so End(W) is the field F_8
// and the residue degree is 3. Same module as `indec.rs` and
// `arquiver.rs`. Hom(W, W) has F_2 dimension 3 and rad End(W) is zero, so
// the radical part of the span starts at zero and one generator fills the
// whole space: the multiplicity is 3 / 3 = 1, while an F_2 basis would give
// 3 copies.
#[test]
fn a_residue_degree_three_summand_gets_one_copy_where_an_fp_basis_gives_three() {
    let field = f2();
    let algebra = kronecker(2, field);
    let identity3 = DenseMat::identity(3);
    let mut companion = DenseMat::zero(3, 3);
    companion.set(0, 1, field.one());
    companion.set(1, 2, field.one());
    companion.set(2, 0, field.one());
    companion.set(2, 1, field.one());
    let w = Module::new(algebra, vec![3, 3], vec![identity3, companion]).unwrap();
    let certified = IndecomposableModule::new(&w).unwrap();
    assert_eq!(certified.residue_degree(), 3, "the fixture must have d = 3");

    let fp_dim = HomSpace::new(&w, &w).unwrap().dim();
    assert_eq!(fp_dim, 3);

    let left = left_approximation(&w, std::slice::from_ref(&w)).unwrap();
    assert_eq!(left.multiplicity(0), fp_dim / 3);
    assert_eq!(left.multiplicity(0), 1);
    assert_eq!(left.map().target().dim_vector(), &[3, 3]);
    assert!(left.map().is_isomorphism());
    assert!(left.verify());
    assert!(left_property_holds(&left));
}

// Take the genuine minimal left approximation f: X -> B and pad it:
// B~ = B (+) N_k with f~ = f followed by the inclusion of B, so the
// component into the extra copy is zero. f~ is still a left approximation,
// since every map that factors through f factors through f~. It is not
// minimal: the projection-inclusion idempotent of the extra copy kills
// f~, and an idempotent outside the radical proves K_{f~} leaves
// rad End(B~).
#[test]
fn a_padded_approximation_is_rejected_by_the_minimality_check() {
    let mut cases = 0;
    for field in fields() {
        for (name, algebra) in fixtures(field) {
            let generators = projectives(&algebra);
            for x in test_modules(&algebra) {
                let a = left_approximation(&x, &generators).unwrap();
                let context = format!("{name} over F_{}", field.modulus());
                let endo = EndoAlgebra::new(a.map().target());
                assert!(
                    radical_coordinates(&endo, a.kernel_basis()).is_ok(),
                    "{context}: the genuine approximation must be minimal"
                );

                let extra = &generators[0];
                let mut parts: Vec<&Module> = a
                    .slots()
                    .iter()
                    .map(|&i| a.summands()[i].module())
                    .collect();
                parts.push(extra);
                let (padded, inclusions, projections) = direct_sum(&parts);
                let mut padded_map = zero_morphism(&x, &padded).unwrap();
                for (c, &i) in a.slots().iter().enumerate() {
                    let component = a
                        .map()
                        .then(&a.projections()[c])
                        .expect("the block projection follows f");
                    assert_eq!(
                        component.target().dim_vector(),
                        a.summands()[i].module().dim_vector()
                    );
                    let block = component.then(&inclusions[c]).unwrap();
                    padded_map = add_morphisms(&padded_map, &block);
                }
                let padded_endo = EndoAlgebra::new(&padded);
                let padded_kernel = left_kernel_of(&padded_map, &padded_endo);
                assert!(
                    radical_coordinates(&padded_endo, &padded_kernel).is_err(),
                    "{context}: the padded approximation must fail minimality"
                );

                // The padded map still approximates: it is the genuine one
                // composed with a split monomorphism.
                let last = projections.len() - 1;
                assert!(
                    padded_map.then(&projections[last]).unwrap().is_zero(),
                    "{context}: the extra component is zero"
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 84);
}

// The same padding on one fixture where every number is hand-derivable,
// so the defect is checked as a value rather than as `is_err()`.
//
// Over A_2 the minimal left add(P)-approximation of P_0 is the identity
// P_0 -> P_0, one copy of P_0. Padding it with a second copy gives
// B~ = P_0 (+) P_0 and f~ = (id, 0). Hom(P_0, P_0) = e_0 A e_0 = k, so
// End(B~) is the 2 by 2 matrix algebra over k: dimension 4, semisimple,
// rad End(B~) = 0. K_{f~} = {h : f~.then(h) = 0} is the set of matrices
// whose first row is zero, of dimension 2. Nothing but zero fits inside a
// zero radical, so the first kernel row already fails and the defect is
// row 0 of a 2-dimensional kernel against a 0-dimensional radical.
#[test]
fn a_padded_approximation_reports_the_kernel_row_outside_the_radical() {
    for field in fields() {
        let algebra = linear_an(2, field);
        let x = Module::projective(&algebra, 0);
        let generators = projectives(&algebra);
        let a = left_approximation(&x, &generators).unwrap();
        assert_eq!(a.slots(), &[0], "the fixture uses one copy of P_0");

        let summands = certify(&generators).unwrap();
        let mut slots = a.slots().to_vec();
        slots.push(a.slots()[0]);
        let (padded, inclusions, _) = slot_sum(&x, &summands, &slots);
        let mut padded_map = zero_morphism(&x, &padded).unwrap();
        for (c, block) in inclusions.iter().enumerate().take(a.slots().len()) {
            let component = a.map().then(&a.projections()[c]).unwrap();
            padded_map = add_morphisms(&padded_map, &component.then(block).unwrap());
        }
        let endo = EndoAlgebra::new(&padded);
        assert_eq!(endo.dim(), 4);
        assert_eq!(endo.radical_dim(), 0);
        let kernel = left_kernel_of(&padded_map, &endo);
        assert_eq!(kernel.rows(), 2);
        let defect = radical_coordinates(&endo, &kernel)
            .map_err(|row| ApproxDefect::KernelOutsideRadical {
                row,
                kernel_dim: kernel.rows(),
                radical_dim: endo.radical_dim(),
            })
            .unwrap_err();
        assert_eq!(
            defect,
            ApproxDefect::KernelOutsideRadical {
                row: 0,
                kernel_dim: 2,
                radical_dim: 0,
            },
            "over F_{}",
            field.modulus()
        );
    }
}

// The same rejection through the public witness. A hand-built
// MinimalLeftApproximation carrying the padded map fails verify(), because
// verify() recomputes K_f and rechecks the radical containment.
#[test]
fn verify_rejects_a_witness_built_around_a_padded_map() {
    let field = f5();
    let algebra = linear_an(3, field);
    let x = Module::projective(&algebra, 0);
    let generators = projectives(&algebra);
    let a = left_approximation(&x, &generators).unwrap();
    assert_eq!(a.slots(), &[0], "the fixture uses one copy of P_0");

    let summands = certify(&generators).unwrap();
    let mut slots = a.slots().to_vec();
    slots.push(a.slots()[0]);
    let (padded, inclusions, projections) = slot_sum(&x, &summands, &slots);
    let mut padded_map = zero_morphism(&x, &padded).unwrap();
    for (c, block) in inclusions.iter().enumerate().take(a.slots().len()) {
        let component = a.map().then(&a.projections()[c]).unwrap();
        padded_map = add_morphisms(&padded_map, &component.then(block).unwrap());
    }
    let factorizations = left_factorizations(&padded_map, &summands);
    let endo = EndoAlgebra::new(&padded);
    let kernel = left_kernel_of(&padded_map, &endo);
    // Every row that is inside the radical gets its true coordinates, so
    // the only claim verify() can reject is the containment itself.
    let radical: Vec<Vec<Fp>> = (0..kernel.rows())
        .map(|r| {
            endo.radical_basis()
                .transpose()
                .solve(kernel.row(r), &field)
                .unwrap_or_else(|| vec![Fp::ZERO; endo.radical_dim()])
        })
        .collect();
    let witness = MinimalLeftApproximation {
        map: padded_map,
        summands,
        slots,
        inclusions,
        projections,
        factorizations,
        kernel,
        radical,
    };
    assert!(!witness.verify(), "a padded map must not verify");
}

#[test]
fn a_decomposable_add_generator_is_rejected_with_its_position() {
    let field = f5();
    let algebra = linear_an(3, field);
    let p0 = Module::projective(&algebra, 0);
    let (sum, _, _) = direct_sum(&[&p0, &p0]);
    let x = Module::simple(&algebra, 0);
    assert_eq!(
        left_approximation(&x, &[p0.clone(), sum]).unwrap_err(),
        ApproxError::SummandNotIndecomposable {
            index: 1,
            reason: IndecError::Decomposable { summands: 2 },
        }
    );
    assert_eq!(
        left_approximation(&x, &[Module::zero(&algebra)]).unwrap_err(),
        ApproxError::SummandNotIndecomposable {
            index: 0,
            reason: IndecError::Zero,
        }
    );
}

#[test]
fn an_isomorphic_repeat_in_the_generator_list_is_rejected() {
    let field = f2();
    let algebra = linear_an(3, field);
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let x = Module::simple(&algebra, 2);
    assert_eq!(
        left_approximation(&x, &[p0.clone(), p1, p0]).unwrap_err(),
        ApproxError::RepeatedSummand {
            first: 0,
            second: 2
        }
    );
}

#[test]
fn a_generator_from_another_algebra_is_a_typed_hom_error() {
    let x = Module::simple(&linear_an(2, f5()), 0);
    let other = Module::simple(&linear_an(2, f5()), 0);
    assert_eq!(
        left_approximation(&x, std::slice::from_ref(&other)).unwrap_err(),
        ApproxError::Hom(HomError::DifferentAlgebras)
    );
}

#[test]
fn error_display_names_the_position_and_the_reason() {
    assert_eq!(
        ApproxError::RepeatedSummand {
            first: 0,
            second: 2
        }
        .to_string(),
        "add-generators 0 and 2 are isomorphic; give one module per class"
    );
    assert_eq!(
        ApproxError::Defect(ApproxDefect::GeneratorGrowth {
            summand: 1,
            growth: 2,
            residue_degree: 3,
        })
        .to_string(),
        "a generator for summand 1 raised the span by 2, not by the residue degree 3; \
         crate defect"
    );
}

// Over the commutative square the four projectives are pairwise
// non-isomorphic and P_0 is projective-injective. The left approximation of
// P_0 by add(P) is the identity, so K_f is zero.
#[test]
fn a_projective_approximated_by_the_projectives_gets_the_identity() {
    for field in fields() {
        let algebra = commutative_square(field);
        let p0 = Module::projective(&algebra, 0);
        let a = left_approximation(&p0, &projectives(&algebra)).unwrap();
        assert_eq!(a.slots(), &[0]);
        assert!(a.map().is_isomorphism());
        assert_eq!(a.kernel_basis().rows(), 0);
        assert!(a.verify());
    }
}
