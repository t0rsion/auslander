use std::sync::Arc;

use crate::decompose::{Certificate, Split, decompose, mutually_inverse};
use crate::indec::IndecomposableModule;
use crate::module::Module;
use crate::profile::{Site, hit};

use super::decomposition::{BasicDecomposition, BasicError, certified};
use super::support::{AddMatch, certified_match};

/// A proof that a module lies in `add(T)`.
///
/// The witness holds the module, its indecomposable summands, `T` with its
/// summands, and for every summand one [`AddMatch`]. Every summand of the
/// module is isomorphic to a summand of `T`, so the module is a direct sum of
/// copies of summands of `T`.
///
/// The summands are stored as [`Module`] values. The indecomposability
/// certificates stay with the [`BasicDecomposition`] inputs the caller holds.
#[derive(Clone)]
pub struct AddClosureWitness {
    pub(super) module: Module,
    pub(super) split: Split,
    pub(super) summands: Vec<Module>,
    pub(super) target: Module,
    pub(super) target_summands: Vec<Module>,
    pub(super) matches: Vec<AddMatch>,
}

debug_fields!(AddClosureWitness |this| {
    "dim_vector" => this.module.dim_vector();
    "target_dim_vector" => this.target.dim_vector();
    "matches" => this.matches.len();
});

// Matches each certified summand against a summand of `t`. `Ok(None)` means
// one summand matched nothing, so the module is outside add(T). Summands of
// `t` are reusable: a module in add(T) may repeat a summand.
fn match_summands(
    summands: &[IndecomposableModule],
    t: &BasicDecomposition,
) -> Result<Option<Vec<AddMatch>>, BasicError> {
    let mut matches = Vec::with_capacity(summands.len());
    for x in summands {
        let Some(matched) = certified_match(x, t.summands().iter().enumerate())? else {
            return Ok(None);
        };
        matches.push(matched);
    }
    Ok(Some(matches))
}

fn summand_modules(summands: &[IndecomposableModule]) -> Vec<Module> {
    summands.iter().map(|x| x.module().clone()).collect()
}

fn add_closure_witness(
    module: Module,
    split: Split,
    summands: &[IndecomposableModule],
    target: &BasicDecomposition,
    matches: Vec<AddMatch>,
) -> AddClosureWitness {
    AddClosureWitness {
        module,
        split,
        summands: summand_modules(summands),
        target: target.module().clone(),
        target_summands: summand_modules(target.summands()),
        matches,
    }
}

impl AddClosureWitness {
    /// Places a basic module in `add(T)`, or reports that it is outside.
    ///
    /// Returns `Ok(None)` when some summand of `m` is isomorphic to no
    /// summand of `t`. Both inputs are basic, so every summand of `m` matches
    /// a different summand of `t`. Use [`AddClosureWitness::from_module`] for
    /// a module that is in `add(T)` without being basic.
    ///
    /// Errors when the inputs do not share one algebra value.
    pub fn new(
        m: &BasicDecomposition,
        t: &BasicDecomposition,
    ) -> Result<Option<AddClosureWitness>, BasicError> {
        if !Arc::ptr_eq(m.module().algebra(), t.module().algebra()) {
            return Err(BasicError::DifferentAlgebras);
        }
        let Some(matches) = match_summands(m.summands(), t)? else {
            return Ok(None);
        };
        Ok(Some(add_closure_witness(
            m.module().clone(),
            m.split().clone(),
            m.summands(),
            t,
            matches,
        )))
    }

    /// Places any module in `add(T)`, with multiplicities.
    ///
    /// A module in `add(T)` need not be basic: `T + T` lies in `add(T)`. This
    /// constructor decomposes `m` without the pairwise-distinct requirement of
    /// [`BasicDecomposition`] and matches each summand separately, so one
    /// summand of `t` can be matched more than once.
    ///
    /// Returns `Ok(None)` when some summand of `m` is isomorphic to no
    /// summand of `t`. An undetermined summand is
    /// [`BasicError::CertificationBlocked`]. Errors when the inputs do not
    /// share one algebra value.
    pub fn from_module(
        m: &Module,
        t: &BasicDecomposition,
    ) -> Result<Option<AddClosureWitness>, BasicError> {
        if !Arc::ptr_eq(m.algebra(), t.module().algebra()) {
            return Err(BasicError::DifferentAlgebras);
        }
        let decomposition = decompose(m);
        for certificate in decomposition.certificates() {
            if let Certificate::Undetermined { attempts } = certificate {
                return Err(BasicError::CertificationBlocked {
                    reason: format!(
                        "a summand stayed undetermined after {attempts} split attempts"
                    ),
                });
            }
        }
        let mut summands = Vec::with_capacity(decomposition.summands().len());
        for endo in decomposition.endos() {
            summands.push(certified(endo.clone())?);
        }
        let Some(matches) = match_summands(&summands, t)? else {
            return Ok(None);
        };
        Ok(Some(add_closure_witness(
            m.clone(),
            decomposition.split().clone(),
            &summands,
            t,
            matches,
        )))
    }

    accessor_methods! {
        /// The module placed in `add(T)`.
        pub module() -> &Module = |this| &this.module;
        /// The indecomposable summands of the module, in decomposition order.
        pub summands() -> &[Module] = |this| &this.summands;
        /// `T` itself.
        pub target() -> &Module = |this| &this.target;
        /// The indecomposable summands of `T`, in decomposition order.
        pub target_summands() -> &[Module] = |this| &this.target_summands;
        /// One match per summand of the module, in summand order.
        pub matches() -> &[AddMatch] = |this| &this.matches;
    }

    /// The verified split whose summands are matched by this witness.
    pub(crate) fn split(&self) -> &Split {
        &self.split
    }

    /// Rechecks the witness: one match per summand, endpoints as recorded,
    /// and each pair of stored maps multiplies to the identity in both
    /// orders.
    pub fn verify(&self) -> bool {
        hit(Site::AddClosureWitnessVerify);
        let split = self.split();
        verify_guard!(split.verify());
        verify_guard!(split.total().ptr_eq(&self.module));
        verify_guard!(
            split.summands().len() == self.summands.len()
                && split
                    .summands()
                    .iter()
                    .zip(&self.summands)
                    .all(|(split, summand)| split.ptr_eq(summand))
        );
        verify_guard!(self.matches.len() == self.summands.len());
        for (x, entry) in self.summands.iter().zip(&self.matches) {
            let_or_false!(Some(y) = self.target_summands.get(entry.target_index));
            verify_guard!(
                entry.forward.source().ptr_eq(x)
                    && entry.forward.target().ptr_eq(y)
                    && entry.backward.source().ptr_eq(y)
                    && entry.backward.target().ptr_eq(x)
            );
            verify_guard!(mutually_inverse(&entry.forward, &entry.backward));
        }
        true
    }
}
