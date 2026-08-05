//! Isomorphism testing with verified witnesses and typed obstructions.
//!
//! [`is_isomorphic`] first tries cheap structural obstructions (dimension
//! vector, radical series), then decomposes both modules ([`decompose`]).
//! A certified-indecomposable pair goes straight to the radical criterion.
//! Anything else gets the Hom-dimension check before summand matching.
//! The radical criterion: for indecomposables with `End(M)` local, `M ≅ N`
//! exactly when some composite `h.then(k)` with `h ∈ Hom(M, N)`,
//! `k ∈ Hom(N, M)` lies outside `rad End(M)`. Such a composite is a unit, so
//! `h` itself is invertible and becomes the witness.
//! An [`IsoOutcome::Isomorphic`] witness is checked to have a two-sided
//! inverse. Every [`IsoOutcome::NotIsomorphic`] carries a proof of
//! non-isomorphism. [`IsoOutcome::Unknown`] is reserved for undetermined
//! summands and never claims either way.

use crate::decompose::{Certificate, Decomposition, add_morphisms, decompose, matrix_inverse};
use crate::endo::EndoAlgebra;
use crate::hom::{HomError, Morphism, hom, identity, zero_morphism};
use crate::module::Module;
use crate::radical::radical;

/// A proof that two modules are not isomorphic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Obstruction {
    /// The dimension vectors differ.
    DimensionVector {
        /// Dimension vector of the first module.
        source: Vec<usize>,
        /// Dimension vector of the second module.
        target: Vec<usize>,
    },
    /// The radical series differ: entry `k` is the dimension vector of
    /// `rad^{k+1}`, listed until it vanishes. An isomorphism maps each
    /// `rad^k M` onto `rad^k N`, so unequal series are proof.
    LoewySeries {
        /// Radical-series dimension vectors of the first module.
        source: Vec<Vec<usize>>,
        /// Radical-series dimension vectors of the second module.
        target: Vec<Vec<usize>>,
    },
    /// Hom-dimension asymmetry: an isomorphism forces
    /// `dim End(M) = dim End(N)` and `dim Hom(M, N) = dim Hom(N, M)`, and one
    /// of the two equalities fails. Symmetric non-isomorphic pairs pass this
    /// check and are decided by summand matching instead.
    HomDimension {
        /// `dim End(M)`.
        end_source: usize,
        /// `dim End(N)`.
        end_target: usize,
        /// `dim Hom(M, N)`.
        forward: usize,
        /// `dim Hom(N, M)`.
        backward: usize,
    },
    /// Both modules are certified indecomposable with equal dimension vectors,
    /// and every composite `Hom(M, N) → Hom(N, M) → End(M)` lies in the
    /// radical, so no homomorphism splits.
    RadicalCriterion,
    /// A certified-indecomposable summand of the first module (with this
    /// dimension vector) matches no unused summand of the second; by
    /// Krull–Schmidt the modules differ.
    UnmatchedSummand {
        /// Dimension vector of the unmatched summand.
        dim_vector: Vec<usize>,
    },
}

/// The outcome of [`is_isomorphic`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IsoOutcome {
    /// An isomorphism, verified invertible with a checked two-sided inverse.
    Isomorphic(Morphism),
    /// A proof of non-isomorphism.
    NotIsomorphic(Obstruction),
    /// Neither a witness nor an obstruction could be certified.
    Unknown {
        /// Why certification failed.
        reason: String,
    },
}

/// The radical criterion for modules certified indecomposable: an isomorphism
/// `m → n`, or `None` when none exists. `endo_m` must be the endomorphism
/// algebra of `m` itself (same module value).
pub(crate) fn indecomposable_iso(m: &Module, n: &Module, endo_m: &EndoAlgebra) -> Option<Morphism> {
    if m.dim_vector() != n.dim_vector() {
        return None;
    }
    let forward = hom(m, n).expect("summands share one algebra and field");
    let backward = hom(n, m).expect("summands share one algebra and field");
    for h in &forward {
        for k in &backward {
            let u = h.then(k).expect("endpoints agree");
            if !endo_m.in_radical(&endo_m.coords(&u)) {
                // u is a unit of the local algebra End(m), so h is invertible.
                return Some(h.clone());
            }
        }
    }
    None
}

fn undetermined_reason(d: &Decomposition) -> Option<String> {
    d.certificates().iter().find_map(|c| match c {
        Certificate::Undetermined { attempts } => Some(format!(
            "a summand stayed undetermined after {attempts} split attempts"
        )),
        Certificate::Indecomposable => None,
    })
}

fn radical_series(m: &Module) -> Vec<Vec<usize>> {
    let mut series = Vec::new();
    let mut layer = radical(m).0;
    while !layer.is_zero() {
        series.push(layer.dim_vector().to_vec());
        layer = radical(&layer).0;
    }
    series
}

fn certified_single(d: &Decomposition) -> bool {
    d.certificates() == [Certificate::Indecomposable]
}

/// Whether `m ≅ n`: a verified witness, a proof of non-isomorphism, or
/// [`IsoOutcome::Unknown`] when neither could be certified. Errors only when
/// the modules do not share one algebra (the same `Arc`) and field.
pub fn is_isomorphic(m: &Module, n: &Module) -> Result<IsoOutcome, HomError> {
    let zero = zero_morphism(m, n)?;
    if m.dim_vector() != n.dim_vector() {
        return Ok(IsoOutcome::NotIsomorphic(Obstruction::DimensionVector {
            source: m.dim_vector().to_vec(),
            target: n.dim_vector().to_vec(),
        }));
    }
    if m.is_zero() {
        return Ok(IsoOutcome::Isomorphic(zero));
    }
    // One module is isomorphic to itself by the identity, whatever the
    // decomposition routes below can certify. Without this the relation is not
    // reflexive in practice: a module whose summands stay undetermined would be
    // reported `Unknown` against itself.
    if Module::ptr_eq(m, n) {
        return Ok(IsoOutcome::Isomorphic(identity(m)));
    }
    let source_series = radical_series(m);
    let target_series = radical_series(n);
    if source_series != target_series {
        return Ok(IsoOutcome::NotIsomorphic(Obstruction::LoewySeries {
            source: source_series,
            target: target_series,
        }));
    }
    let dm = decompose(m);
    let dn = decompose(n);
    // A certified-indecomposable pair goes straight to the radical criterion
    // in the matching loop, which decides it completely; anything else gets
    // the Hom-dimension check first, so an exact obstruction is never
    // suppressed by an undetermined certificate.
    if !(certified_single(&dm) && certified_single(&dn)) {
        let end_source = hom(m, m)?.len();
        let end_target = hom(n, n)?.len();
        let forward = hom(m, n)?.len();
        let backward = hom(n, m)?.len();
        if end_source != end_target || forward != backward {
            return Ok(IsoOutcome::NotIsomorphic(Obstruction::HomDimension {
                end_source,
                end_target,
                forward,
                backward,
            }));
        }
        if let Some(reason) = undetermined_reason(&dm).or_else(|| undetermined_reason(&dn)) {
            return Ok(IsoOutcome::Unknown { reason });
        }
    }
    let mut used = vec![false; dn.summands().len()];
    let mut witness = zero;
    for (i, mi) in dm.summands().iter().enumerate() {
        let endo = EndoAlgebra::new(mi);
        let mut matched = false;
        for (j, nj) in dn.summands().iter().enumerate() {
            if used[j] {
                continue;
            }
            let Some(w) = indecomposable_iso(mi, nj, &endo) else {
                continue;
            };
            used[j] = true;
            let term = dm.split().projections()[i]
                .then(&w)
                .expect("endpoints agree")
                .then(&dn.split().inclusions()[j])
                .expect("endpoints agree");
            witness = add_morphisms(&witness, &term);
            matched = true;
            break;
        }
        if !matched {
            if dm.summands().len() == 1 && dn.summands().len() == 1 {
                return Ok(IsoOutcome::NotIsomorphic(Obstruction::RadicalCriterion));
            }
            return Ok(IsoOutcome::NotIsomorphic(Obstruction::UnmatchedSummand {
                dim_vector: mi.dim_vector().to_vec(),
            }));
        }
    }
    Ok(verified(m, n, witness))
}

// Certifies the assembled witness: per-vertex inverses must form a morphism
// composing to the identity on both sides. Failure would mean a bug upstream,
// so it returns Unknown rather than claiming either way.
fn verified(m: &Module, n: &Module, witness: Morphism) -> IsoOutcome {
    let field = m.field();
    let unknown = |reason: &str| IsoOutcome::Unknown {
        reason: reason.to_string(),
    };
    let mut inverse_maps = Vec::new();
    for v in 0..m.algebra().quiver().num_vertices() {
        match matrix_inverse(witness.map_at(v), &field) {
            Some(inv) => inverse_maps.push(inv),
            None => return unknown("assembled witness is singular at a vertex"),
        }
    }
    match Morphism::new(n, m, inverse_maps) {
        Ok(inverse) => {
            let round = witness.then(&inverse).expect("endpoints agree");
            let round_back = inverse.then(&witness).expect("endpoints agree");
            if round == identity(m) && round_back == identity(n) {
                IsoOutcome::Isomorphic(witness)
            } else {
                unknown("assembled witness has no two-sided inverse")
            }
        }
        Err(_) => unknown("inverse of the assembled witness is not A-linear"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{dual_numbers, kronecker, linear_an};
    use crate::field::PrimeField;
    use crate::linalg::DenseMat;
    use crate::module::direct_sum;

    fn fields() -> [PrimeField; 2] {
        [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
    }

    fn expect_witness(outcome: IsoOutcome, m: &Module, n: &Module) -> Morphism {
        match outcome {
            IsoOutcome::Isomorphic(w) => {
                assert!(w.source().ptr_eq(m) && w.target().ptr_eq(n));
                assert!(w.is_isomorphism());
                w
            }
            other => panic!("expected an isomorphism, got {other:?}"),
        }
    }

    #[test]
    fn a_module_is_isomorphic_to_itself_and_to_a_fresh_copy() {
        for field in fields() {
            let a = linear_an(3);
            let p0 = Module::projective(&a, field, 0);
            expect_witness(is_isomorphic(&p0, &p0).unwrap(), &p0, &p0);
            let copy = Module::projective(&a, field, 0);
            expect_witness(is_isomorphic(&p0, &copy).unwrap(), &p0, &copy);
            let s1 = Module::simple(&a, field, 1);
            let (sum, _, _) = direct_sum(&[&p0, &s1]);
            let (sum2, _, _) = direct_sum(&[&s1, &p0]);
            expect_witness(is_isomorphic(&sum, &sum).unwrap(), &sum, &sum);
            expect_witness(is_isomorphic(&sum, &sum2).unwrap(), &sum, &sum2);
        }
    }

    #[test]
    fn p0_and_i2_over_a3_are_isomorphic() {
        for field in fields() {
            let a = linear_an(3);
            let p0 = Module::projective(&a, field, 0);
            let i2 = Module::injective(&a, field, 2);
            expect_witness(is_isomorphic(&p0, &i2).unwrap(), &p0, &i2);
        }
    }

    #[test]
    fn a_conjugated_module_is_isomorphic_to_the_original() {
        for field in fields() {
            let a = dual_numbers();
            let x = DenseMat::from_rows(&[
                vec![field.zero(), field.one()],
                vec![field.zero(), field.zero()],
            ]);
            let m = Module::new(a.clone(), field, vec![2], vec![x]).unwrap();
            // Conjugate by T = [[1, 1], [0, 1]]: N(a) = T⁻¹ M(a) T.
            let conjugated = DenseMat::from_rows(&[
                vec![field.zero(), field.one()],
                vec![field.zero(), field.zero()],
            ]);
            let conjugated = {
                let t = DenseMat::from_rows(&[
                    vec![field.one(), field.one()],
                    vec![field.zero(), field.one()],
                ]);
                let t_inv = matrix_inverse(&t, &field).unwrap();
                t_inv.mul(&conjugated, &field).mul(&t, &field)
            };
            let n = Module::new(a, field, vec![2], vec![conjugated]).unwrap();
            expect_witness(is_isomorphic(&m, &n).unwrap(), &m, &n);
        }
    }

    #[test]
    fn modules_with_different_dimension_vectors_are_distinguished() {
        for field in fields() {
            let a = linear_an(3);
            let s0 = Module::simple(&a, field, 0);
            let s1 = Module::simple(&a, field, 1);
            assert_eq!(
                is_isomorphic(&s0, &s1).unwrap(),
                IsoOutcome::NotIsomorphic(Obstruction::DimensionVector {
                    source: vec![1, 0, 0],
                    target: vec![0, 1, 0],
                })
            );
        }
    }

    // The two Kronecker representations (a, b) ↦ ([1], [0]) and ([0], [1]) are
    // indecomposable with equal dimension vectors; only the radical criterion
    // tells them apart.
    #[test]
    fn nonisomorphic_kronecker_modules_hit_the_radical_criterion() {
        for field in fields() {
            let a = kronecker(2);
            let m = Module::new(
                a.clone(),
                field,
                vec![1, 1],
                vec![
                    DenseMat::from_rows(&[vec![field.one()]]),
                    DenseMat::from_rows(&[vec![field.zero()]]),
                ],
            )
            .unwrap();
            let n = Module::new(
                a,
                field,
                vec![1, 1],
                vec![
                    DenseMat::from_rows(&[vec![field.zero()]]),
                    DenseMat::from_rows(&[vec![field.one()]]),
                ],
            )
            .unwrap();
            assert_eq!(
                is_isomorphic(&m, &n).unwrap(),
                IsoOutcome::NotIsomorphic(Obstruction::RadicalCriterion)
            );
            expect_witness(is_isomorphic(&m, &m).unwrap(), &m, &m);
        }
    }

    #[test]
    fn an_indecomposable_and_a_semisimple_sum_differ_by_loewy_series() {
        for field in fields() {
            let a = linear_an(2);
            let p0 = Module::projective(&a, field, 0);
            let s0 = Module::simple(&a, field, 0);
            let s1 = Module::simple(&a, field, 1);
            let (sum, _, _) = direct_sum(&[&s0, &s1]);
            assert_eq!(
                is_isomorphic(&p0, &sum).unwrap(),
                IsoOutcome::NotIsomorphic(Obstruction::LoewySeries {
                    source: vec![vec![0, 1]],
                    target: vec![],
                })
            );
            assert_eq!(
                is_isomorphic(&sum, &p0).unwrap(),
                IsoOutcome::NotIsomorphic(Obstruction::LoewySeries {
                    source: vec![],
                    target: vec![vec![0, 1]],
                })
            );
        }
    }

    // The regular Kronecker representation (a, b) ↦ ([1], [λ]) for a scalar λ.
    fn kronecker_regular(
        a: &std::sync::Arc<crate::algebra::MonomialAlgebra>,
        field: PrimeField,
        lambda: i64,
    ) -> Module {
        Module::new(
            a.clone(),
            field,
            vec![1, 1],
            vec![
                DenseMat::from_rows(&[vec![field.one()]]),
                DenseMat::from_rows(&[vec![field.elem(lambda)]]),
            ],
        )
        .unwrap()
    }

    // M ⊕ M vs N ⊕ M with M ≇ N regular: equal dimension vectors and radical
    // series, but dim End is 4 vs 2, so the Hom-dimension check fires before
    // any matching.
    #[test]
    fn endomorphism_dimension_asymmetry_is_a_typed_obstruction() {
        for field in fields() {
            let a = kronecker(2);
            let m = kronecker_regular(&a, field, 0);
            let n = kronecker_regular(&a, field, 1);
            let (mm, _, _) = direct_sum(&[&m, &m]);
            let (nm, _, _) = direct_sum(&[&n, &m]);
            assert_eq!(
                is_isomorphic(&mm, &nm).unwrap(),
                IsoOutcome::NotIsomorphic(Obstruction::HomDimension {
                    end_source: 4,
                    end_target: 2,
                    forward: 2,
                    backward: 2,
                })
            );
        }
    }

    // M_0 ⊕ M_1 vs M_0 ⊕ M_∞: all four Hom dimensions are symmetric
    // (2, 2, 1, 1), so only summand matching can tell them apart.
    #[test]
    fn hom_symmetric_sums_are_distinguished_by_summand_matching() {
        for field in fields() {
            let a = kronecker(2);
            let m0 = kronecker_regular(&a, field, 0);
            let m1 = kronecker_regular(&a, field, 1);
            let minf = Module::new(
                a.clone(),
                field,
                vec![1, 1],
                vec![
                    DenseMat::from_rows(&[vec![field.zero()]]),
                    DenseMat::from_rows(&[vec![field.one()]]),
                ],
            )
            .unwrap();
            let (sum_a, _, _) = direct_sum(&[&m0, &m1]);
            let (sum_b, _, _) = direct_sum(&[&m0, &minf]);
            assert_eq!(
                is_isomorphic(&sum_a, &sum_b).unwrap(),
                IsoOutcome::NotIsomorphic(Obstruction::UnmatchedSummand {
                    dim_vector: vec![1, 1],
                })
            );
        }
    }

    #[test]
    fn zero_modules_are_isomorphic() {
        let field = PrimeField::new(5).unwrap();
        let a = linear_an(3);
        let z1 = Module::zero(&a, field);
        let z2 = Module::zero(&a, field);
        expect_witness(is_isomorphic(&z1, &z2).unwrap(), &z1, &z2);
    }

    #[test]
    fn mismatched_algebras_and_fields_are_rejected() {
        let field = PrimeField::new(5).unwrap();
        let a = linear_an(3);
        let b = linear_an(3);
        let m = Module::simple(&a, field, 0);
        let n = Module::simple(&b, field, 0);
        assert_eq!(
            is_isomorphic(&m, &n).unwrap_err(),
            HomError::DifferentAlgebras
        );
        let other = Module::simple(&a, PrimeField::new(7).unwrap(), 0);
        assert_eq!(
            is_isomorphic(&m, &other).unwrap_err(),
            HomError::DifferentFields
        );
    }
}
