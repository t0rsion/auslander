use std::sync::Arc;

use crate::algebra::Algebra;
use crate::field::PrimeField;
use crate::hom::{Morphism, identity, zero_morphism};
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};

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

display_error! { error SplitError {
    Self::CountMismatch => "summand, inclusion, and projection counts differ";
    Self::EndpointMismatch { index } => "inclusion/projection {index} has wrong endpoints";
    Self::NotIdentityOnSummand { index } => "projection {index} does not split inclusion {index}";
    Self::CrossTermNonzero { from, to } => "inclusion {from} followed by projection {to} is nonzero";
    Self::SumNotIdentity => "the projections and inclusions do not sum to the identity";
} }

/// The direct sum of `parts`, or the zero module over `algebra` when empty.
pub(crate) fn direct_sum_or_zero<'a>(
    algebra: &Arc<Algebra>,
    parts: impl IntoIterator<Item = &'a Module>,
) -> (Module, Vec<Morphism>, Vec<Morphism>) {
    let parts: Vec<&Module> = parts.into_iter().collect();
    match parts.as_slice() {
        [] => (Module::zero(algebra), Vec::new(), Vec::new()),
        _ => direct_sum(&parts),
    }
}

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

/// The inverse morphism when every vertex matrix is square and invertible.
pub(crate) fn inverse_morphism(f: &Morphism) -> Option<Morphism> {
    let field = f.source().field();
    let maps = (0..f.source().algebra().quiver().num_vertices())
        .map(|v| matrix_inverse(f.map_at(v), &field))
        .collect::<Option<Vec<_>>>()?;
    Morphism::new(f.target(), f.source(), maps).ok()
}

/// Whether two morphisms compose to the identity in both orders.
pub(crate) fn mutually_inverse(f: &Morphism, g: &Morphism) -> bool {
    matches!(
        (f.then(g), g.then(f)),
        (Ok(round), Ok(round_back))
            if round == identity(f.source()) && round_back == identity(g.source())
    )
}

fn check_counts(
    summands: &[Module],
    inclusions: &[Morphism],
    projections: &[Morphism],
) -> Result<(), SplitError> {
    if summands.len() != inclusions.len() || summands.len() != projections.len() {
        return Err(SplitError::CountMismatch);
    }
    Ok(())
}

fn check_endpoints(
    total: &Module,
    summands: &[Module],
    inclusions: &[Morphism],
    projections: &[Morphism],
) -> Result<(), SplitError> {
    for (index, summand) in summands.iter().enumerate() {
        let (incl, proj) = (&inclusions[index], &projections[index]);
        if !endpoints_match(total, summand, incl, proj) {
            return Err(SplitError::EndpointMismatch { index });
        }
    }
    Ok(())
}

fn endpoints_match(
    total: &Module,
    summand: &Module,
    inclusion: &Morphism,
    projection: &Morphism,
) -> bool {
    inclusion.source().ptr_eq(summand)
        && inclusion.target().ptr_eq(total)
        && projection.source().ptr_eq(total)
        && projection.target().ptr_eq(summand)
}

fn check_round_trips(
    summands: &[Module],
    inclusions: &[Morphism],
    projections: &[Morphism],
) -> Result<(), SplitError> {
    for (index, summand) in summands.iter().enumerate() {
        let round_trip = inclusions[index]
            .then(&projections[index])
            .expect("endpoints were checked");
        if round_trip != identity(summand) {
            return Err(SplitError::NotIdentityOnSummand { index });
        }
    }
    Ok(())
}

fn check_cross_terms(inclusions: &[Morphism], projections: &[Morphism]) -> Result<(), SplitError> {
    for (from, incl) in inclusions.iter().enumerate() {
        for (to, proj) in projections.iter().enumerate() {
            if from != to && !incl.then(proj).expect("endpoints were checked").is_zero() {
                return Err(SplitError::CrossTermNonzero { from, to });
            }
        }
    }
    Ok(())
}

fn check_sum(
    total: &Module,
    inclusions: &[Morphism],
    projections: &[Morphism],
) -> Result<(), SplitError> {
    let mut sum = zero_morphism(total, total).expect("a module is parallel to itself");
    for (proj, incl) in projections.iter().zip(inclusions) {
        sum = add_morphisms(&sum, &proj.then(incl).expect("endpoints were checked"));
    }
    if sum != identity(total) {
        return Err(SplitError::SumNotIdentity);
    }
    Ok(())
}

fn validate_identities(
    total: &Module,
    summands: &[Module],
    inclusions: &[Morphism],
    projections: &[Morphism],
) -> Result<(), SplitError> {
    check_round_trips(summands, inclusions, projections)?;
    check_cross_terms(inclusions, projections)?;
    check_sum(total, inclusions, projections)?;
    Ok(())
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
        check_counts(&summands, &inclusions, &projections)?;
        check_endpoints(total, &summands, &inclusions, &projections)?;
        validate_identities(total, &summands, &inclusions, &projections)?;
        Ok(Split {
            total: total.clone(),
            summands,
            inclusions,
            projections,
        })
    }

    /// Rechecks every direct-sum identity stored by this split.
    pub fn verify(&self) -> bool {
        Split::new(
            &self.total,
            self.summands.clone(),
            self.inclusions.clone(),
            self.projections.clone(),
        )
        .is_ok()
    }

    accessor_methods! {
        /// The decomposed module.
        pub total() -> &Module = |this| &this.total;
        /// The summands, in inclusion/projection order.
        pub summands() -> &[Module] = |this| &this.summands;
        /// `ι_k: summands[k] → total`.
        pub inclusions() -> &[Morphism] = |this| &this.inclusions;
        /// `π_k: total → summands[k]`.
        pub projections() -> &[Morphism] = |this| &this.projections;
    }
}
