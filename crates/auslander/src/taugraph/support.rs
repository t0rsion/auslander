//! Construction of the regular support tau-tilting pair.

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::basic::{BasicDecomposition, BasicError, ProjectiveSupport};
use crate::context::VerificationContext;
use crate::module::{Module, summand_sum};

/// The module part and the projective support of `(A, 0)`.
pub(super) fn regular_parts(
    algebra: &Arc<Algebra>,
) -> Result<(BasicDecomposition, ProjectiveSupport), BasicError> {
    regular_parts_with(algebra, BasicDecomposition::new)
}

pub(super) fn regular_parts_with(
    algebra: &Arc<Algebra>,
    basic: impl FnOnce(&Module) -> Result<BasicDecomposition, BasicError>,
) -> Result<(BasicDecomposition, ProjectiveSupport), BasicError> {
    let vertices: Vec<u32> = (0..algebra.quiver().num_vertices()).collect();
    let module = summand_sum(algebra, &vertices, Module::projective);
    Ok((basic(&module)?, ProjectiveSupport::new(algebra, &[])?))
}

pub(super) fn regular_parts_with_context(
    algebra: &Arc<Algebra>,
    context: &VerificationContext,
) -> Result<(BasicDecomposition, ProjectiveSupport), BasicError> {
    regular_parts_with(algebra, |module| {
        BasicDecomposition::new_with_context(module, context)
    })
}
