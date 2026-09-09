use std::sync::Arc;

use crate::algebra::Algebra;
use crate::arquiver::IndecomposableCatalog;
use crate::context::VerificationContext;
use crate::decompose::{
    Decomposition, KrullSchmidtOutcome, Split, decompose, direct_sum_or_zero,
    krull_schmidt_from_decomposition,
};
use crate::endo::EndoAlgebra;
use crate::hom::HomError;
use crate::indec::{IndecError, IndecomposableModule};
use crate::iso::indecomposable_iso;
use crate::module::Module;
use crate::profile::{Site, hit};

/// Rejected input, a blocked certification, or a failed internal cross-check
/// of the basic layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BasicError {
    /// A summand could not be certified indecomposable, so nothing is claimed
    /// about the decomposition. The sources are
    /// [`KrullSchmidtOutcome::Unknown`], [`IndecError::Undetermined`], and an
    /// undecided isomorphism test. This is not budget exhaustion.
    CertificationBlocked {
        /// Why certification failed.
        reason: String,
    },
    /// Summands `first` and `second` are isomorphic, so the module is not
    /// basic. The indices count summands in [`BasicDecomposition`] order.
    NotBasic {
        /// Index of the first summand of the isomorphic pair.
        first: usize,
        /// Index of the second summand of the isomorphic pair.
        second: usize,
    },
    /// A support vertex is not a vertex of the algebra's quiver.
    VertexOutOfRange {
        /// The rejected vertex.
        vertex: u32,
        /// The quiver's vertex count.
        num_vertices: u32,
    },
    /// Two inputs do not share one algebra value (the same [`Arc`]).
    DifferentAlgebras,
    /// A morphism operation rejected its input.
    Hom(HomError),
    /// A failed internal cross-check: a theorem's hypotheses hold and the
    /// consequence the code checked did not.
    Defect {
        /// What contradicted the theorem.
        reason: String,
    },
}

display_error! { error BasicError {
    Self::CertificationBlocked { reason } => "certification blocked: {reason}";
    Self::NotBasic { first, second } => "summands {first} and {second} are isomorphic, so the module is not basic";
    Self::VertexOutOfRange { vertex, num_vertices } => "vertex {vertex} is out of range, the quiver has {num_vertices} vertices";
    Self::DifferentAlgebras => "the inputs do not share one algebra";
    Self::Hom(error) => "morphism rejected: {error}";
    Self::Defect { reason } => "internal cross-check failed: {reason}";
} }

from_variants!(BasicError { HomError => Hom });

/// Certifies one summand of a decomposition that already carries an
/// indecomposability certificate. Anything but [`IndecError::Undetermined`]
/// contradicts that certificate, so it is a defect.
///
/// `endo` is the `End` the decomposition already built for that summand, so
/// the gate costs no second radical computation.
pub(super) fn certified(endo: EndoAlgebra) -> Result<IndecomposableModule, BasicError> {
    IndecomposableModule::from_endo(endo).map_err(|error| match error {
        IndecError::Undetermined { attempts } => BasicError::CertificationBlocked {
            reason: format!("a summand stayed undetermined after {attempts} split attempts"),
        },
        other => BasicError::Defect {
            reason: format!("a certified summand failed the indecomposability gate: {other}"),
        },
    })
}

pub(super) fn defect_non_invertible() -> BasicError {
    BasicError::Defect {
        reason: "the radical criterion returned a non-invertible map between certified \
                 indecomposables"
            .to_string(),
    }
}

/// A module with its certified indecomposable summands, pairwise
/// non-isomorphic.
///
/// Fields are private and construction goes through
/// [`BasicDecomposition::new`], so a value of this type proves the module
/// basic. The zero module has zero summands: it is the module part of `(0, A)`.
#[derive(Clone)]
pub struct BasicDecomposition {
    module: Module,
    split: Split,
    summands: Vec<IndecomposableModule>,
}

/// The direct sum of certified summands, in the order given, and the zero
/// module for an empty list.
fn assemble(algebra: &Arc<Algebra>, summands: Vec<IndecomposableModule>) -> BasicDecomposition {
    let (module, inclusions, projections) =
        direct_sum_or_zero(algebra, summands.iter().map(|summand| summand.module()));
    let parts = summands
        .iter()
        .map(|summand| summand.module().clone())
        .collect();
    let split = Split::new(&module, parts, inclusions, projections)
        .expect("a direct sum carries its canonical split");
    BasicDecomposition {
        module,
        split,
        summands,
    }
}

debug_fields!(BasicDecomposition |this| {
    "dim_vector" => this.module.dim_vector();
    "summand_dim_vectors" => this.dim_vectors();
});

impl BasicDecomposition {
    /// Decomposes `m` and requires the summands pairwise non-isomorphic.
    ///
    /// [`crate::decompose::krull_schmidt`] groups the summands into isomorphism classes, each
    /// class representative goes through [`IndecomposableModule::new`], and a
    /// class of multiplicity two or more is [`BasicError::NotBasic`]. A
    /// [`KrullSchmidtOutcome::Unknown`] or an [`IndecError::Undetermined`] is
    /// [`BasicError::CertificationBlocked`]. The zero module gives zero
    /// summands.
    pub fn new(m: &Module) -> Result<BasicDecomposition, BasicError> {
        hit(Site::BasicDecompositionNew);
        let decomposition = decompose(m);
        Self::from_decomposition(m, &decomposition)
    }

    pub(crate) fn new_with_context(
        m: &Module,
        context: &VerificationContext,
    ) -> Result<BasicDecomposition, BasicError> {
        hit(Site::BasicDecompositionNew);
        let decomposition = context.decompose_for(m);
        Self::from_decomposition(m, &decomposition)
    }

    /// Certifies basicness from a decomposition the caller already computed.
    pub(crate) fn from_decomposition(
        m: &Module,
        decomposition: &Decomposition,
    ) -> Result<BasicDecomposition, BasicError> {
        hit(Site::KrullSchmidt);
        if !decomposition.split().total().ptr_eq(m) {
            return Err(BasicError::Defect {
                reason: "the supplied decomposition belongs to another module".to_string(),
            });
        }
        Self::from_krull_schmidt(
            m,
            decomposition.split().clone(),
            krull_schmidt_from_decomposition(decomposition),
        )
    }

    fn from_krull_schmidt(
        m: &Module,
        split: Split,
        outcome: KrullSchmidtOutcome,
    ) -> Result<BasicDecomposition, BasicError> {
        let classes = match outcome {
            KrullSchmidtOutcome::Classes(classes) => classes,
            KrullSchmidtOutcome::Unknown { reason } => {
                return Err(BasicError::CertificationBlocked { reason });
            }
        };
        let mut summands = Vec::with_capacity(classes.len());
        for class in &classes {
            if class.multiplicity > 1 {
                // Classes carry multiplicities, not positions. Listing a class
                // once per copy in class order puts the first repeat directly
                // after the entry counted so far.
                return Err(BasicError::NotBasic {
                    first: summands.len(),
                    second: summands.len() + 1,
                });
            }
            summands.push(certified(class.endo.clone())?);
        }
        Ok(BasicDecomposition {
            module: m.clone(),
            split,
            summands,
        })
    }

    /// This decomposition with the summand at `slot` dropped, or `None` when
    /// `slot` is not a summand position.
    ///
    /// Basicness is inherited, which is why no [`crate::decompose::krull_schmidt`] runs: the
    /// kept summands are a sublist of a pairwise non-isomorphic list, so they
    /// stay pairwise non-isomorphic, and each keeps the certificate it was
    /// built with. The module is reassembled as their direct sum in the same
    /// order. The summand values are the stored ones, so a
    /// [`crate::taurigid::TauCache`] keyed by module identity still hits on
    /// them.
    pub fn without(&self, slot: usize) -> Option<BasicDecomposition> {
        self.summands.get(slot)?;
        let summands: Vec<IndecomposableModule> = self
            .summands
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != slot)
            .map(|(_, x)| x.clone())
            .collect();
        Some(assemble(self.module.algebra(), summands))
    }

    /// This decomposition with `summand` appended.
    ///
    /// Basicness needs exactly one check here. The stored summands are
    /// pairwise non-isomorphic by the invariant and `summand` carries its own
    /// indecomposability certificate, so the only way to lose basicness is
    /// for `summand` to repeat a stored summand. That is one radical
    /// criterion test per stored summand, not a [`crate::decompose::krull_schmidt`] of the sum.
    ///
    /// # Errors
    /// [`BasicError::NotBasic`] when `summand` is isomorphic to the stored
    /// summand `first`, with `second` the position it would have taken.
    /// [`BasicError::DifferentAlgebras`] when `summand` lives over another
    /// algebra value.
    pub fn with_new_summand(
        &self,
        summand: &IndecomposableModule,
    ) -> Result<BasicDecomposition, BasicError> {
        if !Arc::ptr_eq(self.module.algebra(), summand.module().algebra()) {
            return Err(BasicError::DifferentAlgebras);
        }
        for (first, x) in self.summands.iter().enumerate() {
            if indecomposable_iso(summand.module(), x.module(), summand.endo()).is_some() {
                return Err(BasicError::NotBasic {
                    first,
                    second: self.summands.len(),
                });
            }
        }
        let mut summands = self.summands.clone();
        summands.push(summand.clone());
        Ok(assemble(self.module.algebra(), summands))
    }

    /// The decomposition of the sum of the catalog entries listed in
    /// `chosen`, in the order of `chosen`.
    ///
    /// Both catalog enumerators emit one certified entry per isomorphism
    /// class, so distinct entries are pairwise non-isomorphic, distinct
    /// entries are already a basic decomposition, and [`crate::decompose::krull_schmidt`] has
    /// nothing to decide. The summands are the catalog's own module values,
    /// so a [`crate::taurigid::TauCache`] keyed by module identity holds one
    /// translate per catalog entry across every subset.
    ///
    /// # Errors
    /// [`BasicError::NotBasic`] when `chosen` lists one entry twice.
    ///
    /// # Panics
    /// Panics when an entry of `chosen` is not a catalog position.
    pub fn from_catalog(
        catalog: &IndecomposableCatalog,
        chosen: &[usize],
    ) -> Result<BasicDecomposition, BasicError> {
        for (second, &i) in chosen.iter().enumerate() {
            assert!(
                i < catalog.len(),
                "from_catalog: entry {i} is not one of the {} catalog positions",
                catalog.len()
            );
            if let Some(first) = chosen[..second].iter().position(|&j| j == i) {
                return Err(BasicError::NotBasic { first, second });
            }
        }
        let summands: Vec<IndecomposableModule> = chosen
            .iter()
            .map(|&i| (*catalog.entries()[i]).clone())
            .collect();
        Ok(assemble(catalog.algebra(), summands))
    }

    accessor_methods! {
        /// The decomposed module.
        pub module() -> &Module = |this| &this.module;
        /// The certified summands, in decomposition order.
        pub summands() -> &[IndecomposableModule] = |this| &this.summands;
        /// The number of indecomposable summands.
        pub len() -> usize = |this| this.summands.len();
        /// Whether the module is zero, which is the only case with no summands.
        pub is_empty() -> bool = |this| this.summands.is_empty();
    }

    /// The verified split that fixes the stored summand embeddings.
    pub(crate) fn split(&self) -> &Split {
        &self.split
    }

    /// The summand dimension vectors, sorted lexicographically with
    /// repetitions preserved.
    ///
    /// The summands of a basic module are pairwise non-isomorphic, so no
    /// repetition can come from a repeated summand. Two distinct summands can
    /// still share a dimension vector, so the list is not a set: over
    /// `kronecker(2)` three pairwise non-isomorphic indecomposables have the
    /// dimension vector `[1, 1]`.
    pub fn dim_vectors(&self) -> Vec<Vec<usize>> {
        let mut out: Vec<Vec<usize>> = self
            .summands
            .iter()
            .map(|s| s.module().dim_vector().to_vec())
            .collect();
        out.sort();
        out
    }
}
