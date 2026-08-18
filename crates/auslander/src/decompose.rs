//! Direct-sum decomposition: verified splits, idempotent splitting, and
//! certificates.
//!
//! A [`Split`] checks its identities at construction, so holding one is proof of a
//! direct-sum decomposition. [`decompose`] splits until each summand reaches one
//! of two states. In the first, the summand's endomorphism algebra is local, which
//! [`EndoAlgebra`] decides exactly, so the summand is indecomposable
//! ([`Certificate::Indecomposable`]). In the second, every splitting route has run
//! out and nothing is claimed either way ([`Certificate::Undetermined`]).
//!
//! Splitting tries three routes in order: a lifted central idempotent of the
//! semisimple quotient, a constructed non-unit non-nilpotent element, and
//! seeded-random Fitting elements `M = ker(φⁿ) ⊕ im(φⁿ)` with a bounded retry
//! count.
//!
//! `Undetermined` is reachable, not a formality. Every route is bounded, and the
//! constructed route needs a drawn minimal polynomial that is squarefree and
//! reducible, which is likely but not guaranteed.

use std::fmt;

use crate::endo::{EndoAlgebra, SplitMix64};
use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, identity, submodule_with_inclusion, zero_morphism};
use crate::iso::Fingerprint;
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
/// The sum is built with [`Morphism::new_unchecked`]. Both inputs are A-linear
/// for the same `M` and `N`, so at every arrow `a`
/// `(f + g)_{s(a)} · N(a) = f_{s(a)} · N(a) + g_{s(a)} · N(a)`, which is
/// `M(a) · f_{t(a)} + M(a) · g_{t(a)} = M(a) · (f + g)_{t(a)}`: matrix
/// multiplication distributes over addition. The shapes match because the two
/// morphisms share their endpoints, and [`DenseMat::add`] returns canonical
/// entries.
///
/// # Panics
/// Panics unless all endpoints agree in the sense of [`Module::ptr_eq`].
pub(crate) fn add_morphisms(f: &Morphism, g: &Morphism) -> Morphism {
    assert!(
        f.source().ptr_eq(g.source()) && f.target().ptr_eq(g.target()),
        "add_morphisms: endpoints differ"
    );
    let field = f.source().field();
    let maps = (0..f.source().algebra().quiver().num_vertices())
        .map(|v| f.map_at(v).add(g.map_at(v), &field))
        .collect();
    Morphism::new_unchecked(f.source(), f.target(), maps)
}

/// [`DenseMat::inverse`] for callers that hand over a matrix of unknown shape:
/// `None` where that one panics.
pub(crate) fn matrix_inverse(a: &DenseMat, field: &PrimeField) -> Option<DenseMat> {
    (a.rows() == a.cols()).then(|| a.inverse(field))?
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
    /// elements all failed to split. `attempts` counts the Fitting retries alone,
    /// not the retries inside the other two routes. Whether the summand is
    /// indecomposable is not known.
    Undetermined { attempts: u32 },
}

/// A full decomposition: a verified [`Split`] of the input plus one
/// [`Certificate`] and one [`EndoAlgebra`] per summand.
#[derive(Clone, Debug)]
pub struct Decomposition {
    split: Split,
    certificates: Vec<Certificate>,
    endos: Vec<EndoAlgebra>,
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

    /// `End(S_k)` for each summand, in summand order, as the split produced it.
    /// Entry `k` is built from `summands()[k]` itself, so it is the algebra
    /// [`crate::indec::IndecomposableModule::from_endo`] and the radical
    /// criterion want; rebuilding it with [`EndoAlgebra::new`] gives the same
    /// value at the cost of a second radical computation.
    #[inline]
    pub fn endos(&self) -> &[EndoAlgebra] {
        &self.endos
    }
}

/// One isomorphism class of certified-indecomposable summands.
#[derive(Clone, Debug)]
pub struct IsoClass {
    /// The first summand found in the class.
    pub representative: Module,
    /// `End(representative)`, carried over from the split that found it.
    pub endo: EndoAlgebra,
    /// How many summands are isomorphic to the representative.
    pub multiplicity: usize,
}

/// The outcome of [`krull_schmidt`].
#[derive(Clone, Debug)]
pub enum KrullSchmidtOutcome {
    /// Every summand certified indecomposable, grouped into isomorphism
    /// classes; by Krull-Schmidt the multiset of classes is unique.
    Classes(Vec<IsoClass>),
    /// A summand stayed undetermined, so no grouping is claimed.
    Unknown {
        /// Why grouping failed.
        reason: String,
    },
}

/// Decomposes `m` and groups the summands into isomorphism classes with
/// multiplicities, using the radical criterion between certified
/// indecomposables. One undetermined summand makes the whole grouping
/// [`KrullSchmidtOutcome::Unknown`].
///
/// Each class keeps the isomorphism invariants of its representative (the
/// dimension vector, the radical and socle series, `dim End`, and the residue
/// degree), so a summand reaches the radical criterion only against classes
/// those leave open. Every summand's `End` comes from
/// [`Decomposition::endos`]; nothing is rebuilt here.
pub fn krull_schmidt(m: &Module) -> KrullSchmidtOutcome {
    let d = decompose(m);
    let mut classes: Vec<(usize, Fingerprint, usize)> = Vec::new();
    for (k, certificate) in d.certificates().iter().enumerate() {
        if let Certificate::Undetermined { attempts } = certificate {
            return KrullSchmidtOutcome::Unknown {
                reason: format!("a summand stayed undetermined after {attempts} split attempts"),
            };
        }
        let summand = &d.summands()[k];
        let print = Fingerprint::of(summand, &d.endos()[k]);
        match classes.iter_mut().find(|(rep, rep_print, _)| {
            *rep_print == print
                && crate::iso::indecomposable_iso(&d.summands()[*rep], summand, &d.endos()[*rep])
                    .is_some()
        }) {
            Some((_, _, multiplicity)) => *multiplicity += 1,
            None => classes.push((k, print, 1)),
        }
    }
    KrullSchmidtOutcome::Classes(
        classes
            .into_iter()
            .map(|(rep, _, multiplicity)| IsoClass {
                representative: d.summands()[rep].clone(),
                endo: d.endos()[rep].clone(),
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
    if !m.is_zero() {
        let endo = EndoAlgebra::new(m);
        split_recursively(m, endo, identity(m), identity(m), &mut rng, &mut parts);
    }
    let mut summands = Vec::with_capacity(parts.len());
    let mut inclusions = Vec::with_capacity(parts.len());
    let mut projections = Vec::with_capacity(parts.len());
    let mut certificates = Vec::with_capacity(parts.len());
    let mut endos = Vec::with_capacity(parts.len());
    for part in parts {
        summands.push(part.summand);
        inclusions.push(part.include);
        projections.push(part.project);
        certificates.push(part.certificate);
        endos.push(part.endo);
    }
    let split = Split::new(m, summands, inclusions, projections)
        .expect("recursive splits compose to a verified split");
    Decomposition {
        split,
        certificates,
        endos,
    }
}

struct Part {
    summand: Module,
    endo: EndoAlgebra,
    include: Morphism,
    project: Morphism,
    certificate: Certificate,
}

// `include: m → total`, `project: total → m` accumulate the position of `m`
// inside the original module across the recursion. `endo` is `End(m)`: the root
// builds it, and each part inherits its radical from the endomorphism algebra
// of the node it was split off, which is what makes one decomposition cost one
// radical chain instead of one per node.
fn split_recursively(
    m: &Module,
    endo: EndoAlgebra,
    include: Morphism,
    project: Morphism,
    rng: &mut SplitMix64,
    out: &mut Vec<Part>,
) {
    if endo.is_local() {
        out.push(Part {
            summand: m.clone(),
            endo,
            include,
            project,
            certificate: Certificate::Indecomposable,
        });
        return;
    }
    let split = deterministic_split(m, &endo, rng)
        .or_else(|| singular_split(m, &endo, rng))
        .or_else(|| fitting_split(m, &endo, rng));
    let Some(split) = split else {
        out.push(Part {
            summand: m.clone(),
            endo,
            include,
            project,
            certificate: Certificate::Undetermined {
                attempts: FITTING_ATTEMPTS,
            },
        });
        return;
    };
    for k in 0..split.summands().len() {
        let summand = &split.summands()[k];
        if summand.is_zero() {
            continue;
        }
        let summand_endo = EndoAlgebra::from_summand(
            summand,
            &endo,
            &split.inclusions()[k],
            &split.projections()[k],
        );
        let summand_include = split.inclusions()[k]
            .then(&include)
            .expect("inclusion chains compose");
        let summand_project = project
            .then(&split.projections()[k])
            .expect("projection chains compose");
        split_recursively(
            summand,
            summand_endo,
            summand_include,
            summand_project,
            rng,
            out,
        );
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

// The Fitting decomposition along one endomorphism, n = dim_k M. None when the
// split would be trivial: φⁿ injective leaves no kernel, φⁿ zero leaves no image.
fn fitting_split_along(m: &Module, phi: &Morphism) -> Option<Split> {
    let field = m.field();
    let psi = morphism_power(m, phi, m.total_dim());
    let n = m.algebra().quiver().num_vertices();
    let mut kernel = Vec::with_capacity(n as usize);
    let mut image = Vec::with_capacity(n as usize);
    for v in 0..n {
        kernel.push(psi.map_at(v).left_kernel_basis(&field));
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

/// A verified two-summand split from per-vertex row bases of two invariant
/// subspace families, or `None` when they are not complementary.
///
/// Both families must be A-invariant. All three routes into this function pass
/// the image or the kernel of an endomorphism of `m`, so both are submodules.
/// [`submodule_with_inclusion`] would panic on a family that is not.
///
/// The two projections are built with [`Morphism::new_unchecked`]. The loop below
/// returns `None` unless the stacked bases at each vertex are square and
/// invertible, so at that point `M_v` is the vector-space direct sum of the two
/// row spaces `U_v` and `W_v`, and `x · proj_first[v]` reads off the coordinates
/// of the `U_v` part of `x` over `first[v]`. With `U` and `W` both submodules,
/// that projection is A-linear: write `x = u + w` at `s(a)`, then
/// `x M(a) = u M(a) + w M(a)` with `u M(a)` in `U_{t(a)}` and `w M(a)` in
/// `W_{t(a)}`, so projecting after acting and acting after projecting give the
/// same element. In matrices that is the square
/// `proj_first[s(a)] · S(a) = M(a) · proj_first[t(a)]` for the induced `S(a)` of
/// the submodule. The shapes are right because `proj_first[v]` is
/// `dim M_v x k1` and `k1` is `sub1.dim_at(v)`, and the entries come from
/// [`DenseMat::inverse`] over the module's own field. Nothing is claimed on the
/// strength of that argument alone: [`Split::new`] still rechecks every
/// split identity on the returned maps, and returns `None` here if one fails.
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
        // The two row counts add up to the vertex dimension, checked above,
        // so the stack is square.
        let inverse = stacked.inverse(&field)?;
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
    let proj1 = Morphism::new_unchecked(m, &sub1, proj_first);
    let proj2 = Morphism::new_unchecked(m, &sub2, proj_second);
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

    // The corner-ring inheritance must land on the same matrix the radical
    // chain lands on, entry for entry: every consumer of radical coordinates
    // compares them for equality.
    #[test]
    fn inherited_radicals_are_the_freshly_computed_ones() {
        for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
            let a3 = linear_an(3, field);
            let dn = dual_numbers(field);
            let tp = truncated_poly(3, field).unwrap();
            let p0 = Module::projective(&a3, 0);
            let s0 = Module::simple(&a3, 0);
            let s2 = Module::simple(&a3, 2);
            let dual = Module::projective(&dn, 0);
            let trunc = Module::projective(&tp, 0);
            let (a, _, _) = direct_sum(&[&p0, &s0, &s2, &p0]);
            let (b, _, _) = direct_sum(&[&dual, &dual, &Module::simple(&dn, 0)]);
            let (c, _, _) = direct_sum(&[&trunc, &trunc, &trunc]);
            for m in [a, b, c] {
                let d = decompose(&m);
                assert_eq!(d.endos().len(), d.summands().len());
                for (k, summand) in d.summands().iter().enumerate() {
                    let fresh = EndoAlgebra::new(summand);
                    let inherited = &d.endos()[k];
                    assert_eq!(inherited.dim(), fresh.dim(), "summand {k}");
                    assert_eq!(
                        inherited.radical_basis(),
                        fresh.radical_basis(),
                        "summand {k} over F_{}",
                        field.modulus()
                    );
                    assert_eq!(inherited.quotient_dim(), fresh.quotient_dim());
                    assert_eq!(inherited.is_local(), fresh.is_local());
                    assert_eq!(
                        inherited.semisimple_factor_count(),
                        fresh.semisimple_factor_count()
                    );
                    assert!(inherited.module().ptr_eq(summand), "summand {k}");
                }
            }
        }
    }

    #[test]
    fn iso_classes_carry_the_endomorphism_algebra_of_their_representative() {
        let field = PrimeField::new(5).unwrap();
        let a = linear_an(3, field);
        let p0 = Module::projective(&a, 0);
        let s2 = Module::simple(&a, 2);
        let (sum, _, _) = direct_sum(&[&p0, &s2, &p0]);
        for class in classes_of(&sum) {
            assert!(class.endo.module().ptr_eq(&class.representative));
            assert!(class.endo.is_local());
            assert_eq!(
                class.endo.radical_basis(),
                EndoAlgebra::new(&class.representative).radical_basis()
            );
        }
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
