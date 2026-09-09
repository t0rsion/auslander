use crate::endo::EndoAlgebra;
use crate::iso::Fingerprint;
use crate::module::Module;
use crate::profile::{Site, hit};

use super::split::Split;

/// What [`decompose`](super::decompose) proved about one summand.
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
    pub(crate) fn from_parts(
        split: Split,
        certificates: Vec<Certificate>,
        endos: Vec<EndoAlgebra>,
    ) -> Self {
        Self {
            split,
            certificates,
            endos,
        }
    }

    accessor_methods! {
        /// The verified split of the input module.
        pub split() -> &Split = |this| &this.split;
        /// One certificate per summand, in summand order.
        pub certificates() -> &[Certificate] = |this| &this.certificates;
        /// The summands, in certificate order.
        pub summands() -> &[Module] = |this| this.split.summands();
        /// `End(S_k)` for each summand, in summand order, as the split produced it.
        /// Entry `k` is built from `summands()[k]` itself, the algebra
        /// [`crate::indec::IndecomposableModule::from_endo`] and the radical
        /// criterion expect. Rebuilding it with [`EndoAlgebra::new`] gives the
        /// same value at the cost of a second radical computation.
        pub endos() -> &[EndoAlgebra] = |this| &this.endos;
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
    hit(Site::KrullSchmidt);
    let d = super::algorithm::decompose(m);
    krull_schmidt_from_decomposition(&d)
}

pub(crate) fn krull_schmidt_from_decomposition(d: &Decomposition) -> KrullSchmidtOutcome {
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
