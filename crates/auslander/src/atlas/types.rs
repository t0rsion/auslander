/// Resource ceilings for one catalog atlas.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CatalogAtlasLimits {
    /// Maximum number of ordered source-target pairs.
    pub max_pairs: usize,
    /// Maximum number of stored Ext dimensions, including degree zero.
    pub max_ext_cells: usize,
    /// Maximum total number of retained source-resolution terms.
    ///
    /// This count excludes matrix entries allocated inside `resolve`.
    pub max_resolution_terms: usize,
    /// Maximum number of copies materialized in one direct sum.
    pub max_materialized_summands: usize,
    /// Maximum total matrix cells allocated while materializing one direct sum.
    ///
    /// This includes output arrow matrices and relation-check intermediates.
    pub max_materialized_cells: usize,
}

impl Default for CatalogAtlasLimits {
    fn default() -> Self {
        Self {
            max_pairs: 1_000_000,
            max_ext_cells: 10_000_000,
            max_resolution_terms: 10_000_000,
            max_materialized_summands: 1_000_000,
            max_materialized_cells: 10_000_000,
        }
    }
}

/// A resource or index error while building a catalog atlas.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CatalogAtlasError {
    /// The inclusive degree bound has no representable successor.
    DegreeOverflow { degree: usize },
    /// The ordered pair count has no representable product.
    PairCountOverflow { catalog_len: usize },
    /// The Ext-cell count has no representable product.
    ExtCellCountOverflow { pairs: usize, degrees: usize },
    /// The per-source resolution-term bound has no representable successor.
    ResolutionTermOverflow { terms_per_source: usize },
    /// The total resolution-term count has no representable product.
    ResolutionCountOverflow {
        sources: usize,
        terms_per_source: usize,
    },
    /// The ordered pair count exceeds the caller ceiling.
    PairLimit { requested: usize, limit: usize },
    /// The Ext-cell count exceeds the caller ceiling.
    ExtCellLimit { requested: usize, limit: usize },
    /// The resolution-term count exceeds the caller ceiling.
    ResolutionTermLimit { requested: usize, limit: usize },
}

display_error! { error CatalogAtlasError {
    Self::DegreeOverflow { degree } => "Ext degree {degree} has no representable successor";
    Self::PairCountOverflow { catalog_len } => "the catalog pair count overflows for {catalog_len} entries";
    Self::ExtCellCountOverflow { pairs, degrees } => "the Ext-cell count overflows for {pairs} pairs and {degrees} degrees";
    Self::ResolutionTermOverflow { terms_per_source } => "one source resolution needs {terms_per_source} terms, but that count overflows";
    Self::ResolutionCountOverflow { sources, terms_per_source } => "the resolution-term count overflows for {sources} sources and {terms_per_source} terms per source";
    Self::PairLimit { requested, limit } => "the catalog atlas needs {requested} ordered pairs, above the limit {limit}";
    Self::ExtCellLimit { requested, limit } => "the catalog atlas needs {requested} Ext cells, above the limit {limit}";
    Self::ResolutionTermLimit { requested, limit } => "the catalog atlas needs {requested} resolution terms, above the limit {limit}";
} }

/// Exact operation counts for one catalog atlas.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CatalogAtlasWork {
    /// Ordered source-target pairs stored in the atlas.
    pub pairs: usize,
    /// Ext dimensions stored in the atlas.
    pub ext_cells: usize,
    /// Source resolutions retained by the atlas.
    pub resolutions: usize,
    /// Resolution terms retained by the atlas.
    pub resolution_terms: usize,
    /// Ext tables computed from retained source resolutions.
    pub ext_tables: usize,
}

/// One ordered source-target row in a catalog Ext table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CatalogExtRow {
    source: usize,
    target: usize,
    dimensions: Vec<usize>,
}

impl CatalogExtRow {
    pub(crate) fn new(source: usize, target: usize, dimensions: Vec<usize>) -> Self {
        Self {
            source,
            target,
            dimensions,
        }
    }

    accessor_methods! {
        /// The source catalog index.
        pub source() -> usize = |this| this.source;
        /// The target catalog index.
        pub target() -> usize = |this| this.target;
        /// Ext dimensions in degrees zero through the atlas bound.
        pub dimensions() -> &[usize] = |this| &this.dimensions;
    }
}

/// Ordered Ext dimensions for every pair in one catalog.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CatalogExtTable {
    catalog_len: usize,
    max_degree: usize,
    rows: Vec<CatalogExtRow>,
}

impl CatalogExtTable {
    pub(crate) fn new(catalog_len: usize, max_degree: usize, rows: Vec<CatalogExtRow>) -> Self {
        Self {
            catalog_len,
            max_degree,
            rows,
        }
    }

    accessor_methods! {
        /// The number of catalog entries indexed by this table.
        pub catalog_len() -> usize = |this| this.catalog_len;
        /// The inclusive largest stored Ext degree.
        pub max_degree() -> usize = |this| this.max_degree;
        /// Rows in source-major, target-major order.
        pub rows() -> &[CatalogExtRow] = |this| &this.rows;
        /// The number of ordered pair rows.
        pub len() -> usize = |this| this.rows.len();
        /// Whether no ordered pair rows are stored.
        pub is_empty() -> bool = |this| this.rows.is_empty();
    }

    /// Returns one ordered pair row by its source and target indices.
    pub fn row(&self, source: usize, target: usize) -> Option<&CatalogExtRow> {
        let index = source
            .checked_mul(self.catalog_len)
            .and_then(|offset| offset.checked_add(target))?;
        (source < self.catalog_len && target < self.catalog_len).then(|| &self.rows[index])
    }

    /// Returns the Ext dimensions for one ordered pair.
    pub fn dimensions(&self, source: usize, target: usize) -> Option<&[usize]> {
        self.row(source, target).map(CatalogExtRow::dimensions)
    }

    /// Returns one stored Ext dimension.
    pub fn dim(&self, source: usize, target: usize, degree: usize) -> Option<usize> {
        self.dimensions(source, target)
            .and_then(|dimensions| dimensions.get(degree).copied())
    }
}

/// Nonnegative multiplicities in catalog entry order.
pub type MultiplicityVector = Vec<usize>;

/// Limits for one multiplicity enumeration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MultiplicityLimits {
    /// Maximum number of retained solutions.
    pub max_solutions: usize,
    /// Maximum number of search states visited.
    pub max_nodes: usize,
}

impl Default for MultiplicityLimits {
    fn default() -> Self {
        Self {
            max_solutions: 1_000_000,
            max_nodes: 10_000_000,
        }
    }
}

/// A malformed target dimension vector or a checked search-counter overflow.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultiplicityError {
    /// The target has one entry per quiver vertex.
    DimensionVectorLength { expected: usize, got: usize },
    /// The visited-state counter has no representable successor.
    NodeCountOverflow,
    /// The iterative search stack could not reserve its checked depth.
    NodeStackAllocationFailed { requested: usize },
}

display_error! { error MultiplicityError {
    Self::DimensionVectorLength { expected, got } => "target dimension vector has {got} entries, expected {expected}";
    Self::NodeCountOverflow => "multiplicity search node count overflows usize";
    Self::NodeStackAllocationFailed { requested } => "multiplicity search stack allocation failed for {requested} entries";
} }

/// A malformed multiplicity vector or an oversized direct-sum request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtlasMaterializeError {
    /// The vector needs one entry per catalog module.
    MultiplicityLength { expected: usize, got: usize },
    /// The requested copy count exceeds the caller ceiling.
    SummandLimit { requested: usize, limit: usize },
    /// The requested copy count does not fit in `usize`.
    SummandCountOverflow,
    /// A repeated module dimension does not fit in `usize`.
    DimensionProductOverflow {
        index: usize,
        vertex: usize,
        multiplicity: usize,
        dimension: usize,
    },
    /// The direct-sum dimension does not fit in `usize`.
    DimensionSumOverflow { vertex: usize },
    /// The sum of vertex dimensions does not fit in `usize`.
    TotalDimensionOverflow,
    /// A materialized matrix shape does not fit in `usize` cells.
    CellProductOverflow { rows: usize, columns: usize },
    /// The total materialized cell count does not fit in `usize`.
    CellCountOverflow,
    /// The materialized output and relation checks exceed the caller ceiling.
    CellLimit { requested: usize, limit: usize },
    /// The copy-reference list could not reserve its checked size.
    AllocationFailed { requested: usize },
}

display_error! { error AtlasMaterializeError {
    Self::MultiplicityLength { expected, got } => "multiplicity vector has {got} entries, expected {expected}";
    Self::SummandLimit { requested, limit } => "direct-sum request needs {requested} summands, above the limit {limit}";
    Self::SummandCountOverflow => "direct-sum summand count overflows usize";
    Self::DimensionProductOverflow { index, vertex, multiplicity, dimension } => "multiplicity {multiplicity} at catalog index {index} overflows dimension {dimension} at vertex {vertex}";
    Self::DimensionSumOverflow { vertex } => "direct-sum dimension overflows at vertex {vertex}";
    Self::TotalDimensionOverflow => "direct-sum total dimension overflows usize";
    Self::CellProductOverflow { rows, columns } => "materialized matrix shape {rows}x{columns} overflows its cell count";
    Self::CellCountOverflow => "materialized matrix cell count overflows usize";
    Self::CellLimit { requested, limit } => "materialized matrices need {requested} cells, above the limit {limit}";
    Self::AllocationFailed { requested } => "direct-sum reference list allocation failed for {requested} summands";
} }
