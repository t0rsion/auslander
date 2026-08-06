//! Direct-sum decomposition: verified splits, idempotent splitting, and
//! certificates.
//!
//! A [`Split`] checks its identities at construction, so holding one is proof
//! of a direct-sum decomposition. [`decompose`] splits until every summand
//! either has a local endomorphism algebra (certificate
//! [`Certificate::Indecomposable`], exact via [`EndoAlgebra`]) or has
//! exhausted every splitting route (certificate
//! [`Certificate::Undetermined`]). Splitting tries three routes in order: a
//! lifted central idempotent of the semisimple quotient, a constructed
//! non-unit non-nilpotent element, and seeded-random Fitting elements
//! `M = ker(φⁿ) ⊕ im(φⁿ)` with a bounded retry count.
//!
//! `Undetermined` is reachable. Every route is bounded, and the constructed
//! route needs a drawn minimal polynomial that is squarefree and reducible,
//! which is likely but not guaranteed.

use std::fmt;

use crate::endo::{EndoAlgebra, SplitMix64};
use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, identity, submodule_with_inclusion, zero_morphism};
use crate::linalg::DenseMat;
use crate::module::Module;

/// Rejected split data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SplitError {
    /// `summands`, `inclusions`, and `projections` need equal lengths.
    CountMismatch,
    /// Inclusion or projection `index` does not run between summand `index`
    /// and the total module (by [`Module::ptr_eq`]).
    EndpointMismatch { index: usize },
    /// `inclusions[index].then(&projections[index])` is not the identity.
    NotIdentityOnSummand { index: usize },
    /// `inclusions[from].then(&projections[to])` is nonzero for `from != to`.
    CrossTermNonzero { from: usize, to: usize },
    /// `Σ_k projections[k].then(&inclusions[k])` is not the identity.
    SumNotIdentity,
}

impl fmt::Display for SplitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CountMismatch => f.write_str("summand, inclusion, and projection counts differ"),
            Self::EndpointMismatch { index } => {
                write!(f, "inclusion/projection {index} has wrong endpoints")
            }
            Self::NotIdentityOnSummand { index } => {
                write!(f, "projection {index} does not split inclusion {index}")
            }
            Self::CrossTermNonzero { from, to } => {
                write!(f, "inclusion {from} followed by projection {to} is nonzero")
            }
            Self::SumNotIdentity => {
                f.write_str("the projections and inclusions do not sum to the identity")
            }
        }
    }
}

impl std::error::Error for SplitError {}

/// A verified direct-sum decomposition `M ≅ ⊕_k S_k`: inclusions `ι_k: S_k → M`
/// and projections `π_k: M → S_k` with `ι_k.then(π_k) = id`,
/// `ι_j.then(π_k) = 0` for `j ≠ k`, and `Σ_k π_k.then(ι_k) = id_M`, all checked
/// at construction.
#[derive(Clone, Debug)]
pub struct Split {
    total: Module,
    summands: Vec<Module>,
    inclusions: Vec<Morphism>,
    projections: Vec<Morphism>,
}

/// The sum of parallel morphisms.
///
/// # Panics
/// Panics unless all endpoints agree in the sense of [`Module::ptr_eq`].
pub(crate) fn add_morphisms(a: &Morphism, b: &Morphism) -> Morphism {
    assert!(
        a.source().ptr_eq(b.source()) && a.target().ptr_eq(b.target()),
        "add_morphisms: endpoints differ"
    );
    let field = a.source().field();
    let maps = (0..a.source().algebra().quiver().num_vertices())
        .map(|v| a.map_at(v).add(b.map_at(v), &field))
        .collect();
    Morphism::new(a.source(), a.target(), maps).expect("a sum of A-linear maps is A-linear")
}

/// The inverse of a square matrix, or `None` when singular.
pub(crate) fn matrix_inverse(a: &DenseMat, field: &PrimeField) -> Option<DenseMat> {
    if a.rows() != a.cols() || a.rank(field) < a.rows() {
        return None;
    }
    let n = a.rows();
    let mut inv = DenseMat::zero(n, n);
    for j in 0..n {
        let mut unit = vec![Fp::ZERO; n];
        unit[j] = Fp::ONE;
        let col = a.solve(&unit, field)?;
        for (i, &v) in col.iter().enumerate() {
            inv.set(i, j, v);
        }
    }
    Some(inv)
}

impl Split {
    /// Builds a split after verifying every identity. The summand order fixes
    /// the inclusion and projection order.
    pub fn new(
        total: &Module,
        summands: Vec<Module>,
        inclusions: Vec<Morphism>,
        projections: Vec<Morphism>,
    ) -> Result<Split, SplitError> {
        if summands.len() != inclusions.len() || summands.len() != projections.len() {
            return Err(SplitError::CountMismatch);
        }
        for (index, summand) in summands.iter().enumerate() {
            let (incl, proj) = (&inclusions[index], &projections[index]);
            if !incl.source().ptr_eq(summand)
                || !incl.target().ptr_eq(total)
                || !proj.source().ptr_eq(total)
                || !proj.target().ptr_eq(summand)
            {
                return Err(SplitError::EndpointMismatch { index });
            }
        }
        for (index, summand) in summands.iter().enumerate() {
            let round_trip = inclusions[index]
                .then(&projections[index])
                .expect("endpoints were checked");
            if round_trip != identity(summand) {
                return Err(SplitError::NotIdentityOnSummand { index });
            }
        }
        for (from, incl) in inclusions.iter().enumerate() {
            for (to, proj) in projections.iter().enumerate() {
                if from != to && !incl.then(proj).expect("endpoints were checked").is_zero() {
                    return Err(SplitError::CrossTermNonzero { from, to });
                }
            }
        }
        let mut sum = zero_morphism(total, total).expect("a module is parallel to itself");
        for (proj, incl) in projections.iter().zip(&inclusions) {
            sum = add_morphisms(&sum, &proj.then(incl).expect("endpoints were checked"));
        }
        if sum != identity(total) {
            return Err(SplitError::SumNotIdentity);
        }
        Ok(Split {
            total: total.clone(),
            summands,
            inclusions,
            projections,
        })
    }

    /// The decomposed module.
    #[inline]
    pub fn total(&self) -> &Module {
        &self.total
    }

    /// The summands, in inclusion/projection order.
    #[inline]
    pub fn summands(&self) -> &[Module] {
        &self.summands
    }

    /// `ι_k: summands[k] → total`.
    #[inline]
    pub fn inclusions(&self) -> &[Morphism] {
        &self.inclusions
    }

    /// `π_k: total → summands[k]`.
    #[inline]
    pub fn projections(&self) -> &[Morphism] {
        &self.projections
    }
}

/// What [`decompose`] proved about one summand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Certificate {
    /// The summand's endomorphism algebra is local (exact radical and factor
    /// count), so the summand is indecomposable.
    Indecomposable,
    /// No splitting route succeeded: the deterministic idempotent route and the
    /// constructed non-unit route found nothing, and `attempts` seeded Fitting
    /// elements all failed to split. `attempts` is the Fitting retry budget
    /// alone; it does not count the retries inside the other two routes.
    /// The summand may or may not be indecomposable.
    Undetermined { attempts: u32 },
}

/// A full decomposition: a verified [`Split`] of the input plus one
/// [`Certificate`] per summand.
#[derive(Clone, Debug)]
pub struct Decomposition {
    split: Split,
    certificates: Vec<Certificate>,
}

impl Decomposition {
    /// The verified split of the input module.
    #[inline]
    pub fn split(&self) -> &Split {
        &self.split
    }

    /// One certificate per summand, in summand order.
    #[inline]
    pub fn certificates(&self) -> &[Certificate] {
        &self.certificates
    }

    /// The summands, in certificate order.
    #[inline]
    pub fn summands(&self) -> &[Module] {
        self.split.summands()
    }
}

/// One isomorphism class of certified-indecomposable summands.
#[derive(Clone, Debug)]
pub struct IsoClass {
    /// The first summand found in the class.
    pub representative: Module,
    /// How many summands are isomorphic to the representative.
    pub multiplicity: usize,
}

/// The outcome of [`krull_schmidt`].
#[derive(Clone, Debug)]
pub enum KrullSchmidtOutcome {
    /// Every summand certified indecomposable, grouped into isomorphism
    /// classes; by Krull–Schmidt the multiset of classes is unique.
    Classes(Vec<IsoClass>),
    /// A summand stayed undetermined, so no grouping is claimed.
    Unknown {
        /// Why grouping failed.
        reason: String,
    },
}

/// Decomposes `m` and groups the summands into isomorphism classes with
/// multiplicities, using the radical criterion between certified
/// indecomposables.
pub fn krull_schmidt(m: &Module) -> KrullSchmidtOutcome {
    let d = decompose(m);
    let mut classes: Vec<(Module, EndoAlgebra, usize)> = Vec::new();
    for (summand, certificate) in d.summands().iter().zip(d.certificates()) {
        if let Certificate::Undetermined { attempts } = certificate {
            return KrullSchmidtOutcome::Unknown {
                reason: format!("a summand stayed undetermined after {attempts} split attempts"),
            };
        }
        match classes
            .iter_mut()
            .find(|(rep, endo, _)| crate::iso::indecomposable_iso(rep, summand, endo).is_some())
        {
            Some((_, _, multiplicity)) => *multiplicity += 1,
            None => classes.push((summand.clone(), EndoAlgebra::new(summand), 1)),
        }
    }
    KrullSchmidtOutcome::Classes(
        classes
            .into_iter()
            .map(|(representative, _, multiplicity)| IsoClass {
                representative,
                multiplicity,
            })
            .collect(),
    )
}

const FITTING_ATTEMPTS: u32 = 64;
const DECOMPOSE_SEED: u64 = 0x000a_0512_a11d_e12b;

/// Splits `m` into summands with certificates; the zero module decomposes into
/// no summands. Deterministic: all randomness is seeded per call.
pub fn decompose(m: &Module) -> Decomposition {
    let mut rng = SplitMix64(DECOMPOSE_SEED);
    let mut parts = Vec::new();
    split_recursively(m, identity(m), identity(m), &mut rng, &mut parts);
    let mut summands = Vec::with_capacity(parts.len());
    let mut inclusions = Vec::with_capacity(parts.len());
    let mut projections = Vec::with_capacity(parts.len());
    let mut certificates = Vec::with_capacity(parts.len());
    for (summand, incl, proj, certificate) in parts {
        summands.push(summand);
        inclusions.push(incl);
        projections.push(proj);
        certificates.push(certificate);
    }
    let split = Split::new(m, summands, inclusions, projections)
        .expect("recursive splits compose to a verified split");
    Decomposition {
        split,
        certificates,
    }
}

type Part = (Module, Morphism, Morphism, Certificate);

// `include: m → total`, `project: total → m` accumulate the position of `m`
// inside the original module across the recursion.
fn split_recursively(
    m: &Module,
    include: Morphism,
    project: Morphism,
    rng: &mut SplitMix64,
    out: &mut Vec<Part>,
) {
    if m.is_zero() {
        return;
    }
    let endo = EndoAlgebra::new(m);
    if endo.is_local() {
        out.push((m.clone(), include, project, Certificate::Indecomposable));
        return;
    }
    let split = deterministic_split(m, &endo, rng)
        .or_else(|| singular_split(m, &endo, rng))
        .or_else(|| fitting_split(m, &endo, rng));
    let Some(split) = split else {
        let certificate = Certificate::Undetermined {
            attempts: FITTING_ATTEMPTS,
        };
        out.push((m.clone(), include, project, certificate));
        return;
    };
    for k in 0..split.summands().len() {
        let part = &split.summands()[k];
        let part_include = split.inclusions()[k]
            .then(&include)
            .expect("inclusion chains compose");
        let part_project = project
            .then(&split.projections()[k])
            .expect("projection chains compose");
        split_recursively(part, part_include, part_project, rng, out);
    }
}

// M = im(e) ⊕ im(1 − e) for a lifted idempotent e of End(M).
fn deterministic_split(m: &Module, endo: &EndoAlgebra, rng: &mut SplitMix64) -> Option<Split> {
    let e = endo.morphism(&endo.split_idempotent(rng)?);
    let field = m.field();
    let n = m.algebra().quiver().num_vertices();
    let mut first = Vec::with_capacity(n as usize);
    let mut second = Vec::with_capacity(n as usize);
    for v in 0..n {
        let ev = e.map_at(v);
        let mut complement = DenseMat::identity(ev.rows());
        for r in 0..ev.rows() {
            for c in 0..ev.cols() {
                complement.set(r, c, field.sub(complement.get(r, c), ev.get(r, c)));
            }
        }
        first.push(ev.row_space_basis(&field));
        second.push(complement.row_space_basis(&field));
    }
    split_from_bases(m, first, second)
}

// M = ker(φⁿ) ⊕ im(φⁿ) for a φ that is neither invertible nor nilpotent,
// which is what makes both parts nonzero. Such a φ is constructed rather than
// drawn: see EndoAlgebra::singular_element for why sampling does not find one.
fn singular_split(m: &Module, endo: &EndoAlgebra, rng: &mut SplitMix64) -> Option<Split> {
    let coords = endo.singular_element(rng, FITTING_ATTEMPTS)?;
    fitting_split_along(m, &endo.morphism(&coords))
}

// M = ker(φⁿ) ⊕ im(φⁿ), n = dim_k M, for seeded-random φ; both parts are
// nonzero exactly when the image of φ in End/rad is a nonzero non-unit.
fn fitting_split(m: &Module, endo: &EndoAlgebra, rng: &mut SplitMix64) -> Option<Split> {
    let field = m.field();
    let p = field.modulus();
    for _ in 0..FITTING_ATTEMPTS {
        let coords: Vec<Fp> = (0..endo.dim())
            .map(|_| field.elem(rng.below(p) as i64))
            .collect();
        if let Some(split) = fitting_split_along(m, &endo.morphism(&coords)) {
            return Some(split);
        }
    }
    None
}

// The Fitting decomposition along one endomorphism, or None when φⁿ is either
// injective or zero and the split would be trivial.
fn fitting_split_along(m: &Module, phi: &Morphism) -> Option<Split> {
    let field = m.field();
    let psi = morphism_power(m, phi, m.total_dim());
    let n = m.algebra().quiver().num_vertices();
    let mut kernel = Vec::with_capacity(n as usize);
    let mut image = Vec::with_capacity(n as usize);
    for v in 0..n {
        kernel.push(psi.map_at(v).transpose().kernel_basis(&field));
        image.push(psi.map_at(v).row_space_basis(&field));
    }
    if kernel.iter().all(|b| b.rows() == 0) || image.iter().all(|b| b.rows() == 0) {
        return None;
    }
    split_from_bases(m, kernel, image)
}

fn morphism_power(m: &Module, phi: &Morphism, mut exp: usize) -> Morphism {
    let mut base = phi.clone();
    let mut acc = identity(m);
    while exp > 0 {
        if exp & 1 == 1 {
            acc = acc.then(&base).expect("endomorphisms compose");
        }
        base = base.then(&base).expect("endomorphisms compose");
        exp >>= 1;
    }
    acc
}

// A verified two-summand split from per-vertex row bases of two invariant
// subspace families, or `None` when they are not complementary.
fn split_from_bases(m: &Module, first: Vec<DenseMat>, second: Vec<DenseMat>) -> Option<Split> {
    let field = m.field();
    let n = m.algebra().quiver().num_vertices() as usize;
    let mut proj_first = Vec::with_capacity(n);
    let mut proj_second = Vec::with_capacity(n);
    for v in 0..n {
        let k1 = first[v].rows();
        let k2 = second[v].rows();
        if k1 + k2 != m.dim_vector()[v] {
            return None;
        }
        let mut stacked = DenseMat::zero(k1 + k2, m.dim_vector()[v]);
        for r in 0..k1 {
            for c in 0..first[v].cols() {
                stacked.set(r, c, first[v].get(r, c));
            }
        }
        for r in 0..k2 {
            for c in 0..second[v].cols() {
                stacked.set(k1 + r, c, second[v].get(r, c));
            }
        }
        let inverse = matrix_inverse(&stacked, &field)?;
        let mut p1 = DenseMat::zero(inverse.rows(), k1);
        let mut p2 = DenseMat::zero(inverse.rows(), k2);
        for r in 0..inverse.rows() {
            for c in 0..k1 {
                p1.set(r, c, inverse.get(r, c));
            }
            for c in 0..k2 {
                p2.set(r, c, inverse.get(r, k1 + c));
            }
        }
        proj_first.push(p1);
        proj_second.push(p2);
    }
    let (sub1, incl1) = submodule_with_inclusion(m, first);
    let (sub2, incl2) = submodule_with_inclusion(m, second);
    let proj1 = Morphism::new(m, &sub1, proj_first).ok()?;
    let proj2 = Morphism::new(m, &sub2, proj_second).ok()?;
    Split::new(m, vec![sub1, sub2], vec![incl1, incl2], vec![proj1, proj2]).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{dual_numbers, kronecker, linear_an, truncated_poly};
    use crate::iso::{IsoOutcome, is_isomorphic};
    use crate::module::direct_sum;

    fn fields() -> [PrimeField; 2] {
        [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
    }

    fn sorted_dims(summands: &[Module]) -> Vec<Vec<usize>> {
        let mut dims: Vec<Vec<usize>> = summands.iter().map(|s| s.dim_vector().to_vec()).collect();
        dims.sort();
        dims
    }

    #[test]
    fn split_new_accepts_direct_sum_data_and_rejects_swapped_projections() {
        let field = PrimeField::new(5).unwrap();
        let a = linear_an(3, field);
        let p0 = Module::projective(&a, 0);
        let p0_copy = Module::projective(&a, 0);
        let (sum, inclusions, projections) = direct_sum(&[&p0, &p0_copy]);
        let summands = vec![p0.clone(), p0_copy.clone()];
        assert!(
            Split::new(
                &sum,
                summands.clone(),
                inclusions.clone(),
                projections.clone()
            )
            .is_ok()
        );
        let swapped_endpoints = Split::new(
            &sum,
            vec![p0_copy.clone(), p0.clone()],
            inclusions.clone(),
            projections.clone(),
        );
        assert_eq!(
            swapped_endpoints.unwrap_err(),
            SplitError::EndpointMismatch { index: 0 }
        );
        assert_eq!(
            Split::new(&sum, summands.clone(), inclusions.clone(), Vec::new()).unwrap_err(),
            SplitError::CountMismatch
        );
        // π_1 in slot 0 has the wrong target module, caught as endpoints.
        let reordered = vec![projections[1].clone(), projections[0].clone()];
        assert_eq!(
            Split::new(&sum, summands, inclusions, reordered).unwrap_err(),
            SplitError::EndpointMismatch { index: 0 }
        );
    }

    #[test]
    fn split_new_rejects_a_projection_that_does_not_split_its_inclusion() {
        let field = PrimeField::new(5).unwrap();
        let a = linear_an(3, field);
        let p0 = Module::projective(&a, 0);
        let (sum, inclusions, projections) = direct_sum(&[&p0]);
        let zero = zero_morphism(&sum, &p0).unwrap();
        assert_eq!(
            Split::new(
                &sum,
                vec![p0.clone()],
                inclusions.clone(),
                vec![zero.clone()]
            )
            .unwrap_err(),
            SplitError::NotIdentityOnSummand { index: 0 }
        );
        let zero_incl = zero_morphism(&p0, &sum).unwrap();
        assert_eq!(
            Split::new(&sum, vec![p0.clone()], vec![zero_incl], projections).unwrap_err(),
            SplitError::NotIdentityOnSummand { index: 0 }
        );
        assert_eq!(
            Split::new(&sum, vec![p0.clone()], inclusions, vec![zero]).unwrap_err(),
            SplitError::NotIdentityOnSummand { index: 0 }
        );
    }

    #[test]
    fn split_new_rejects_a_partial_family_of_summands() {
        let field = PrimeField::new(5).unwrap();
        let a = linear_an(3, field);
        let p0 = Module::projective(&a, 0);
        let s2 = Module::simple(&a, 2);
        let (sum, inclusions, projections) = direct_sum(&[&p0, &s2]);
        // Dropping the second summand leaves Σ π ι ≠ id on the total.
        assert_eq!(
            Split::new(
                &sum,
                vec![p0.clone()],
                vec![inclusions[0].clone()],
                vec![projections[0].clone()]
            )
            .unwrap_err(),
            SplitError::SumNotIdentity
        );
    }

    // End(M ⊕ M) ≅ M_2(F_4) has one Wedderburn factor, so the deterministic
    // idempotent route finds nothing and only the seeded Fitting fallback can
    // split; both summands must come back certified and isomorphic to M.
    #[test]
    fn decompose_splits_the_f4_kronecker_double_via_the_fitting_fallback() {
        let field = PrimeField::new(2).unwrap();
        let a = kronecker(2, field);
        let id = DenseMat::from_rows(&[
            vec![field.one(), field.zero()],
            vec![field.zero(), field.one()],
        ]);
        // Companion matrix of x² + x + 1, irreducible over F_2.
        let c = DenseMat::from_rows(&[
            vec![field.zero(), field.one()],
            vec![field.one(), field.one()],
        ]);
        let m = Module::new(a, vec![2, 2], vec![id, c]).unwrap();
        let (sum, _, _) = direct_sum(&[&m, &m]);
        let d = decompose(&sum);
        assert_eq!(d.summands().len(), 2);
        assert_eq!(
            d.certificates(),
            &[Certificate::Indecomposable, Certificate::Indecomposable]
        );
        for s in d.summands() {
            assert!(matches!(
                is_isomorphic(s, &m).unwrap(),
                IsoOutcome::Isomorphic(_)
            ));
        }
    }

    #[test]
    fn decompose_of_the_zero_module_has_no_summands() {
        let a = linear_an(3, PrimeField::new(5).unwrap());
        let d = decompose(&Module::zero(&a));
        assert!(d.summands().is_empty());
        assert!(d.certificates().is_empty());
    }

    #[test]
    fn decompose_of_indecomposables_is_a_single_certified_summand() {
        for field in fields() {
            let a3 = linear_an(3, field);
            let dn = dual_numbers(field);
            for m in [
                Module::projective(&a3, 0),
                Module::simple(&a3, 1),
                Module::projective(&dn, 0),
            ] {
                let d = decompose(&m);
                assert_eq!(d.summands().len(), 1);
                assert_eq!(d.certificates(), &[Certificate::Indecomposable]);
                assert_eq!(d.summands()[0].dim_vector(), m.dim_vector());
            }
        }
    }

    #[test]
    fn decompose_of_p0_plus_s2_finds_both_certified_summands() {
        for field in fields() {
            let a = linear_an(3, field);
            let p0 = Module::projective(&a, 0);
            let s2 = Module::simple(&a, 2);
            let (sum, _, _) = direct_sum(&[&p0, &s2]);
            let d = decompose(&sum);
            assert_eq!(d.summands().len(), 2);
            assert!(
                d.certificates()
                    .iter()
                    .all(|c| *c == Certificate::Indecomposable)
            );
            assert_eq!(
                sorted_dims(d.summands()),
                vec![vec![0, 0, 1], vec![1, 1, 1]]
            );
        }
    }

    // End(S ⊕ S) ≅ M_2(F_p) has one Wedderburn factor, so the deterministic
    // route finds nothing and only seeded Fitting elements can split.
    #[test]
    fn decompose_of_two_isomorphic_simples_splits_via_the_fitting_fallback() {
        for field in fields() {
            let a = linear_an(3, field);
            let s = Module::simple(&a, 0);
            let (sum, _, _) = direct_sum(&[&s, &s]);
            let endo = EndoAlgebra::new(&sum);
            assert!(
                deterministic_split(&sum, &endo, &mut SplitMix64(DECOMPOSE_SEED)).is_none(),
                "the central route cannot split a matrix algebra"
            );
            let d = decompose(&sum);
            assert_eq!(d.summands().len(), 2);
            assert!(
                d.certificates()
                    .iter()
                    .all(|c| *c == Certificate::Indecomposable)
            );
            assert_eq!(
                sorted_dims(d.summands()),
                vec![vec![1, 0, 0], vec![1, 0, 0]]
            );
        }
    }

    #[test]
    fn decompose_of_the_truncated_polynomial_square_finds_two_local_summands() {
        for field in fields() {
            let a = truncated_poly(3, field).unwrap();
            let p = Module::projective(&a, 0);
            let (sum, _, _) = direct_sum(&[&p, &p]);
            let d = decompose(&sum);
            assert_eq!(d.summands().len(), 2);
            assert_eq!(sorted_dims(d.summands()), vec![vec![3], vec![3]]);
            assert!(
                d.certificates()
                    .iter()
                    .all(|c| *c == Certificate::Indecomposable)
            );
        }
    }

    fn classes_of(m: &Module) -> Vec<IsoClass> {
        match krull_schmidt(m) {
            KrullSchmidtOutcome::Classes(classes) => classes,
            KrullSchmidtOutcome::Unknown { reason } => panic!("unexpected Unknown: {reason}"),
        }
    }

    fn class_dims(classes: &[IsoClass]) -> Vec<(Vec<usize>, usize)> {
        let mut dims: Vec<(Vec<usize>, usize)> = classes
            .iter()
            .map(|c| (c.representative.dim_vector().to_vec(), c.multiplicity))
            .collect();
        dims.sort();
        dims
    }

    #[test]
    fn krull_schmidt_of_p_plus_s_plus_p_has_multiplicities_2_and_1() {
        for field in fields() {
            let a = linear_an(3, field);
            let p0 = Module::projective(&a, 0);
            let s2 = Module::simple(&a, 2);
            let (sum, _, _) = direct_sum(&[&p0, &s2, &p0]);
            let classes = classes_of(&sum);
            assert_eq!(
                class_dims(&classes),
                vec![(vec![0, 0, 1], 1), (vec![1, 1, 1], 2)]
            );
        }
    }

    #[test]
    fn krull_schmidt_is_invariant_under_permutation_of_summands() {
        for field in fields() {
            let a = linear_an(3, field);
            let s0 = Module::simple(&a, 0);
            let p1 = Module::projective(&a, 1);
            let (shuffled, _, _) = direct_sum(&[&s0, &p1, &s0, &p1]);
            let (reordered, _, _) = direct_sum(&[&p1, &s0, &p1, &s0]);
            let left = classes_of(&shuffled);
            let right = classes_of(&reordered);
            assert_eq!(class_dims(&left), class_dims(&right));
            assert_eq!(
                class_dims(&left),
                vec![(vec![0, 1, 1], 2), (vec![1, 0, 0], 2)]
            );
            for class in &left {
                let partner = right
                    .iter()
                    .find(|c| c.representative.dim_vector() == class.representative.dim_vector())
                    .expect("matching class exists");
                assert!(matches!(
                    crate::iso::is_isomorphic(&class.representative, &partner.representative)
                        .unwrap(),
                    crate::iso::IsoOutcome::Isomorphic(_)
                ));
            }
        }
    }

    #[test]
    fn krull_schmidt_of_an_indecomposable_is_a_single_class() {
        let field = PrimeField::new(5).unwrap();
        let a = dual_numbers(field);
        let p = Module::projective(&a, 0);
        let classes = classes_of(&p);
        assert_eq!(classes.len(), 1);
        assert_eq!(classes[0].multiplicity, 1);
        assert_eq!(classes[0].representative.dim_vector(), &[2]);
    }

    #[test]
    fn krull_schmidt_of_the_zero_module_has_no_classes() {
        let a = linear_an(3, PrimeField::new(2).unwrap());
        let z = Module::zero(&a);
        assert!(classes_of(&z).is_empty());
    }

    #[test]
    fn decompose_is_deterministic_across_calls() {
        let field = PrimeField::new(2).unwrap();
        let a = linear_an(3, field);
        let s = Module::simple(&a, 0);
        let p1 = Module::projective(&a, 1);
        let (sum, _, _) = direct_sum(&[&s, &p1, &s]);
        let first = decompose(&sum);
        let second = decompose(&sum);
        let dims = |d: &Decomposition| -> Vec<Vec<usize>> {
            d.summands()
                .iter()
                .map(|s| s.dim_vector().to_vec())
                .collect()
        };
        assert_eq!(dims(&first), dims(&second));
        assert_eq!(first.certificates(), second.certificates());
        for (a, b) in first
            .split()
            .inclusions()
            .iter()
            .zip(second.split().inclusions())
        {
            for v in 0..3 {
                assert_eq!(a.map_at(v), b.map_at(v));
            }
        }
    }
}
