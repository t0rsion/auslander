use super::super::*;
use super::{CatalogExtRow, CatalogExtTable};
use auslander::atlas_artifact::{
    CatalogAtlasArtifactExtRow, CatalogAtlasArtifactResultRow, CatalogAtlasArtifactStatus,
};

/// One ordered source-target Ext row in a catalog atlas.
#[pyclass(name = "CatalogExtRow", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogExtRow {
    pub(crate) inner: CatalogExtRow,
}

#[pymethods]
impl PyCatalogExtRow {
    #[getter]
    fn source(&self) -> usize {
        self.inner.source()
    }

    #[getter]
    fn target(&self) -> usize {
        self.inner.target()
    }

    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        self.inner.dimensions().to_vec()
    }

    #[getter]
    fn vanishes(&self) -> bool {
        self.inner
            .dimensions()
            .iter()
            .all(|&dimension| dimension == 0)
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogExtRow(source={}, target={}, dimensions={:?})",
            self.source(),
            self.target(),
            self.inner.dimensions()
        )
    }
}

/// The source-major, target-major Ext table stored by a catalog atlas.
#[pyclass(name = "CatalogExtTable", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogExtTable {
    pub(crate) inner: CatalogExtTable,
}

#[pymethods]
impl PyCatalogExtTable {
    #[getter]
    fn catalog_len(&self) -> usize {
        self.inner.catalog_len()
    }

    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.max_degree()
    }

    #[getter]
    fn rows(&self) -> Vec<PyCatalogExtRow> {
        self.inner
            .rows()
            .iter()
            .cloned()
            .map(|inner| PyCatalogExtRow { inner })
            .collect()
    }

    /// Returns one ordered pair row, or `None` for an outside index.
    #[pyo3(signature = (source, target))]
    fn row(&self, source: usize, target: usize) -> Option<PyCatalogExtRow> {
        self.inner
            .row(source, target)
            .cloned()
            .map(|inner| PyCatalogExtRow { inner })
    }

    /// Returns one ordered pair's dimensions, or `None` for an outside index.
    #[pyo3(signature = (source, target))]
    fn dimensions(&self, source: usize, target: usize) -> Option<Vec<usize>> {
        self.inner.dimensions(source, target).map(<[usize]>::to_vec)
    }

    /// Returns one stored Ext dimension, or `None` outside the table.
    #[pyo3(signature = (source, target, degree))]
    fn dim(&self, source: usize, target: usize, degree: usize) -> Option<usize> {
        self.inner.dim(source, target, degree)
    }

    fn __len__(&self) -> usize {
        self.inner.rows().len()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogExtTable(catalog_len={}, max_degree={}, rows={})",
            self.catalog_len(),
            self.max_degree(),
            self.inner.rows().len()
        )
    }
}

/// One ordered Ext row stored in a portable catalog atlas artifact.
#[pyclass(name = "CatalogAtlasArtifactExtRow", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogAtlasArtifactExtRow {
    pub(crate) inner: CatalogAtlasArtifactExtRow,
}

#[pymethods]
impl PyCatalogAtlasArtifactExtRow {
    #[getter]
    fn source(&self) -> usize {
        self.inner.source()
    }

    #[getter]
    fn target(&self) -> usize {
        self.inner.target()
    }

    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        self.inner.dimensions().to_vec()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogAtlasArtifactExtRow(source={}, target={}, dimensions={:?})",
            self.source(),
            self.target(),
            self.inner.dimensions()
        )
    }
}

/// One multiplicity vector and its cached self-Ext scores in an artifact.
#[pyclass(name = "CatalogAtlasArtifactResultRow", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogAtlasArtifactResultRow {
    pub(crate) inner: CatalogAtlasArtifactResultRow,
}

#[pymethods]
impl PyCatalogAtlasArtifactResultRow {
    #[getter]
    fn multiplicities(&self) -> Vec<usize> {
        self.inner.multiplicities().to_vec()
    }

    #[getter]
    fn self_ext(&self) -> Vec<usize> {
        self.inner.self_ext().to_vec()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogAtlasArtifactResultRow(multiplicities={:?}, self_ext={:?})",
            self.inner.multiplicities(),
            self.inner.self_ext()
        )
    }
}

/// Complete or cut status for the multiplicity rows in an artifact.
#[pyclass(name = "CatalogAtlasArtifactStatus", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogAtlasArtifactStatus {
    pub(crate) inner: CatalogAtlasArtifactStatus,
}

#[pymethods]
impl PyCatalogAtlasArtifactStatus {
    /// `complete` or `cut`.
    #[getter]
    fn kind(&self) -> &'static str {
        if self.inner.is_complete() {
            "complete"
        } else {
            "cut"
        }
    }

    #[getter]
    fn is_complete(&self) -> bool {
        self.inner.is_complete()
    }

    #[getter]
    fn is_cut(&self) -> bool {
        self.inner.is_cut()
    }

    /// The retained prefix length, or `None` for a complete enumeration.
    #[getter]
    fn coverage(&self) -> Option<usize> {
        self.inner.coverage()
    }

    /// The typed budget that stopped a cut, or `None` for a complete result.
    #[getter]
    fn cut_reason(&self) -> Option<PyMultiplicityCutReason> {
        self.inner
            .cut_reason()
            .map(|inner| PyMultiplicityCutReason { inner })
    }

    /// Search states visited before a cut.
    #[getter]
    fn nodes_visited(&self) -> Option<usize> {
        self.inner.nodes_visited()
    }

    fn __repr__(&self) -> String {
        format!("CatalogAtlasArtifactStatus(kind={:?})", self.kind())
    }
}
