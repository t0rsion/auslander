use super::*;

/// The canonical representatives in `0..p` of a row of field elements. An `Fp`
/// keeps its representative to itself outside the library, so the row travels
/// through a one-row matrix.
pub(crate) fn row_u64(row: &[Fp]) -> Vec<u64> {
    DenseMat::from_rows(&[row.to_vec()])
        .entries_u64()
        .pop()
        .expect("one row in, one row out")
}

/// The nonzero entries of a matrix as `(row, column, value)` triples.
pub(crate) fn sparse_entries(matrix: &DenseMat) -> Vec<(usize, usize, u64)> {
    let mut entries = Vec::new();
    for (row, values) in matrix.entries_u64().into_iter().enumerate() {
        for (column, value) in values.into_iter().enumerate() {
            if value != 0 {
                entries.push((row, column, value));
            }
        }
    }
    entries
}

/// One matrix from a list of integer rows, entries reduced mod p. A matrix given
/// as zero rows carries no column count of its own, so `cols_when_empty` supplies
/// the expected one; raises ValueError on rows of differing lengths.
pub(crate) fn dense_from_rows(
    field: PrimeField,
    rows: &[Vec<i64>],
    cols_when_empty: usize,
    what: &str,
) -> PyResult<DenseMat> {
    let cols = rows.first().map_or(cols_when_empty, Vec::len);
    let mut mat = DenseMat::zero(rows.len(), cols);
    for (r, row) in rows.iter().enumerate() {
        if row.len() != cols {
            return Err(PyValueError::new_err(format!(
                "{what} has rows of differing lengths ({} vs {cols})",
                row.len()
            )));
        }
        for (c, &v) in row.iter().enumerate() {
            mat.set(r, c, field.elem(v));
        }
    }
    Ok(mat)
}

/// One matrix from `(row, column, value)` entries. Each coordinate occurs at
/// most once, and entries are reduced modulo the field characteristic.
pub(crate) fn dense_from_sparse(
    field: PrimeField,
    rows: usize,
    columns: usize,
    entries: &[(usize, usize, i64)],
    what: &str,
) -> PyResult<DenseMat> {
    let mut matrix = DenseMat::zero(rows, columns);
    let mut seen = BTreeSet::new();
    for (position, &(row, column, value)) in entries.iter().enumerate() {
        if row >= rows || column >= columns {
            return Err(PyValueError::new_err(format!(
                "{what} entry {position} has coordinate ({row}, {column}) outside {rows} x {columns}"
            )));
        }
        if !seen.insert((row, column)) {
            return Err(PyValueError::new_err(format!(
                "{what} repeats coordinate ({row}, {column})"
            )));
        }
        matrix.set(row, column, field.elem(value));
    }
    Ok(matrix)
}

pub(crate) fn check_sparse_module_shape(
    quiver: &Quiver,
    dims: &[usize],
    map_count: usize,
) -> PyResult<()> {
    if dims.len() != quiver.num_vertices() as usize {
        return Err(PyValueError::new_err(format!(
            "module has {} vertex dimensions, expected {}",
            dims.len(),
            quiver.num_vertices()
        )));
    }
    if map_count != quiver.num_arrows() {
        return Err(PyValueError::new_err(format!(
            "module has {map_count} arrow maps, expected {}",
            quiver.num_arrows()
        )));
    }
    Ok(())
}

/// One Python wrapper per item of a slice, in the slice's order.
pub(crate) fn wrap_all<'a, T, W: From<&'a T>>(items: &'a [T]) -> Vec<W> {
    items.iter().map(W::from).collect()
}

/// The dimension vectors of the terms of a resolution or coresolution, in
/// term order.
pub(crate) fn dim_vectors(terms: &[Module]) -> Vec<Vec<usize>> {
    terms.iter().map(|t| t.dim_vector().to_vec()).collect()
}

/// A Python-owned copy of a resolution stored inside another certificate.
pub(crate) fn wrapped_resolution(module: &Module, inner: &ProjectiveResolution) -> PyResolution {
    PyResolution {
        module: module.clone(),
        inner: ProjectiveResolution {
            terms: inner.terms.clone(),
            maps: inner.maps.clone(),
            augmentation: inner.augmentation.clone(),
            end: inner.end,
        },
    }
}

/// How a resolution prefix ended, as the `status=` field of a repr.
pub(crate) fn end_repr(end: ResolutionEnd) -> String {
    match end {
        ResolutionEnd::Finite => "finite".to_string(),
        ResolutionEnd::Cut { at } => format!("('cut', {at})"),
    }
}

/// The completion limits, each omitted keyword keeping the default.
pub(crate) fn limits_from(
    max_basis: Option<usize>,
    max_word_len: Option<usize>,
    max_steps: Option<usize>,
    max_origin_terms: Option<usize>,
    max_ambiguities: Option<usize>,
) -> CompletionLimits {
    let mut limits = CompletionLimits::default();
    if let Some(n) = max_basis {
        limits.max_basis = n;
    }
    if let Some(n) = max_word_len {
        limits.max_word_len = n;
    }
    if let Some(n) = max_steps {
        limits.max_steps = n;
    }
    if let Some(n) = max_origin_terms {
        limits.max_origin_terms = n;
    }
    if let Some(n) = max_ambiguities {
        limits.max_ambiguities = n;
    }
    limits
}

/// The mutation-graph budgets, each omitted keyword keeping the default.
pub(crate) fn graph_limits_from(
    max_vertices: Option<usize>,
    max_directed_mutations: Option<usize>,
    max_work_units: Option<u64>,
    max_matrix_entries: Option<usize>,
) -> MutationGraphLimits {
    let mut limits = MutationGraphLimits::default();
    if let Some(n) = max_vertices {
        limits.max_vertices = n;
    }
    if let Some(n) = max_directed_mutations {
        limits.max_directed_mutations = n;
    }
    if let Some(n) = max_work_units {
        limits.max_work_units = n;
    }
    if let Some(n) = max_matrix_entries {
        limits.max_matrix_entries = n;
    }
    limits
}

/// The modules as one direct sum over `algebra`, and the zero module for an
/// empty list. Raises ValueError naming the first module built from another
/// algebra object or over another field.
pub(crate) fn assembled(algebra: &Arc<Algebra>, modules: &[Module]) -> PyResult<Module> {
    for (i, m) in modules.iter().enumerate() {
        if !Arc::ptr_eq(m.algebra(), algebra) {
            return Err(PyValueError::new_err(format!(
                "module {i} was built from another algebra object or over another field; \
                 a pair needs every summand over the algebra it is taken over"
            )));
        }
    }
    let refs: Vec<&Module> = modules.iter().collect();
    if refs.is_empty() {
        return Ok(Module::zero(algebra));
    }
    Ok(direct_sum(&refs).0)
}

/// The two parts of a candidate pair: the direct sum of `modules` decomposed
/// and checked basic, and the projective support of `vertices`.
pub(crate) fn pair_parts(
    algebra: &Arc<Algebra>,
    modules: &[Module],
    vertices: &[u32],
) -> PyResult<(BasicDecomposition, ProjectiveSupport)> {
    let sum = assembled(algebra, modules)?;
    let module = BasicDecomposition::new(&sum).map_err(basic_error)?;
    let projective = ProjectiveSupport::new(algebra, vertices).map_err(basic_error)?;
    Ok((module, projective))
}
