use std::sync::Arc;

use crate::algebra::Algebra;
use crate::arquiver::{CatalogProvenance, IndecomposableCatalog};
use crate::ext::ext_table_from_resolution;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::ArrowId;
use crate::resolution::{ProjectiveResolution, ResolutionEnd, resolve};

use super::types::{
    AtlasMaterializeError, CatalogAtlasError, CatalogAtlasLimits, CatalogAtlasWork, CatalogExtRow,
    CatalogExtTable,
};

/// Reusable Ext dimensions and source resolutions for one complete catalog.
#[derive(Clone)]
pub struct CatalogAtlas {
    catalog: Arc<IndecomposableCatalog>,
    max_degree: usize,
    limits: CatalogAtlasLimits,
    table: CatalogExtTable,
    resolutions: Vec<Arc<ProjectiveResolution>>,
    work: CatalogAtlasWork,
}

debug_fields! { CatalogAtlas |this| {
    "catalog_len" => this.catalog.len();
    "max_degree" => this.max_degree;
    "work" => this.work;
} }

impl CatalogAtlas {
    /// Builds all ordered Ext tables through `max_degree`.
    ///
    /// Degree zero stores `Hom`. Every source resolution is retained and is
    /// shared by all target rows. Pair, cell, and resolution-term limits are
    /// checked before resolution work. Resolution matrix allocations are not
    /// counted by `max_resolution_terms`.
    pub fn compute(
        catalog: Arc<IndecomposableCatalog>,
        max_degree: usize,
        limits: CatalogAtlasLimits,
    ) -> Result<Self, CatalogAtlasError> {
        let (pairs, cells, terms) = preflight(catalog.len(), max_degree, limits)?;
        let resolutions = build_resolutions(&catalog, max_degree, terms, limits)?;
        let table = build_table(&catalog, &resolutions, max_degree, pairs);
        let resolution_terms = resolutions
            .iter()
            .map(|resolution| resolution.terms.len())
            .try_fold(0usize, usize::checked_add)
            .expect("preflight bounds the retained resolution terms");
        Ok(Self {
            catalog,
            max_degree,
            limits,
            table,
            resolutions,
            work: CatalogAtlasWork {
                pairs,
                ext_cells: cells,
                resolutions: terms.0,
                resolution_terms,
                ext_tables: pairs,
            },
        })
    }

    accessor_methods! {
        /// The complete catalog shared by this atlas.
        pub catalog() -> &Arc<IndecomposableCatalog> = |this| &this.catalog;
        /// The number of indecomposable entries in the catalog.
        pub catalog_len() -> usize = |this| this.catalog.len();
        /// The algebra shared by every catalog entry and table endpoint.
        pub algebra() -> &Arc<Algebra> = |this| this.catalog.algebra();
        /// The classification theorem behind catalog completeness.
        pub provenance() -> CatalogProvenance = |this| this.catalog.provenance();
        /// The inclusive largest stored Ext degree.
        pub max_degree() -> usize = |this| this.max_degree;
        /// The checked resource ceilings used by this atlas.
        pub limits() -> CatalogAtlasLimits = |this| this.limits;
        /// The reusable ordered Ext table.
        pub ext_table() -> &CatalogExtTable = |this| &this.table;
        /// The ordered Ext rows in source-major, target-major order.
        pub pairs() -> &[CatalogExtRow] = |this| this.table.rows();
        /// Exact operation counts for the stored atlas.
        pub work() -> CatalogAtlasWork = |this| this.work;
    }

    /// Returns the dimensions of one ordered catalog pair in degrees zero through the bound.
    pub fn ext_dimensions(&self, source: usize, target: usize) -> Option<&[usize]> {
        self.table.dimensions(source, target)
    }

    /// Returns one stored ordered Ext dimension.
    pub fn ext_dim(&self, source: usize, target: usize, degree: usize) -> Option<usize> {
        self.table.dim(source, target, degree)
    }

    /// Returns one retained source resolution.
    pub fn resolution(&self, source: usize) -> Option<&ProjectiveResolution> {
        self.resolutions.get(source).map(Arc::as_ref)
    }

    /// Returns the end status of one retained source resolution.
    pub fn resolution_end(&self, source: usize) -> Option<ResolutionEnd> {
        self.resolution(source).map(|resolution| resolution.end)
    }

    /// Returns the number of vertices in the catalog algebra.
    pub(crate) fn vertex_count(&self) -> usize {
        self.algebra().quiver().num_vertices() as usize
    }

    /// Returns entry dimension vectors in catalog order.
    pub(crate) fn entry_dimensions(&self) -> Vec<Vec<usize>> {
        self.catalog
            .entries()
            .iter()
            .map(|entry| entry.module().dim_vector().to_vec())
            .collect()
    }

    /// Materializes a direct sum in catalog order without decomposing it.
    pub fn materialize(&self, multiplicities: &[usize]) -> Result<Module, AtlasMaterializeError> {
        let (modules, dimensions) = self.materialization_data(multiplicities)?;
        if modules.is_empty() {
            return Ok(Module::zero(self.algebra()));
        }
        Ok(materialized_sum(self.algebra(), &modules, dimensions))
    }

    fn materialization_data<'a>(
        &'a self,
        multiplicities: &[usize],
    ) -> Result<(Vec<&'a Module>, Vec<usize>), AtlasMaterializeError> {
        if multiplicities.len() != self.catalog.len() {
            return Err(AtlasMaterializeError::MultiplicityLength {
                expected: self.catalog.len(),
                got: multiplicities.len(),
            });
        }
        let count = checked_summand_count(multiplicities, self.limits.max_materialized_summands)?;
        let dimensions = self.dimensions_for_multiplicities(multiplicities)?;
        let cells = materialized_cell_count(self.algebra(), &dimensions)?;
        if cells > self.limits.max_materialized_cells {
            return Err(AtlasMaterializeError::CellLimit {
                requested: cells,
                limit: self.limits.max_materialized_cells,
            });
        }
        let modules = expand_modules(&self.catalog, multiplicities, count)?;
        Ok((modules, dimensions))
    }

    fn dimensions_for_multiplicities(
        &self,
        multiplicities: &[usize],
    ) -> Result<Vec<usize>, AtlasMaterializeError> {
        let mut dimensions = vec![0usize; self.vertex_count()];
        for (index, (&multiplicity, entry)) in multiplicities
            .iter()
            .zip(self.catalog.entries())
            .enumerate()
        {
            add_entry_dimensions(
                &mut dimensions,
                index,
                multiplicity,
                entry.module().dim_vector(),
            )?;
        }
        check_total_dimension(&dimensions)?;
        Ok(dimensions)
    }

    /// Recomputes the atlas and compares every retained table and resolution.
    pub fn verify(&self) -> bool {
        let Ok(rebuilt) = Self::compute(self.catalog.clone(), self.max_degree, self.limits) else {
            return false;
        };
        self.table == rebuilt.table
            && self.work == rebuilt.work
            && self.resolutions.len() == rebuilt.resolutions.len()
            && self
                .resolutions
                .iter()
                .zip(&rebuilt.resolutions)
                .all(|(left, right)| left.agrees_with(right))
    }
}

fn preflight(
    catalog_len: usize,
    max_degree: usize,
    limits: CatalogAtlasLimits,
) -> Result<(usize, usize, (usize, usize)), CatalogAtlasError> {
    let degrees = max_degree
        .checked_add(1)
        .ok_or(CatalogAtlasError::DegreeOverflow { degree: max_degree })?;
    let pairs = catalog_len
        .checked_mul(catalog_len)
        .ok_or(CatalogAtlasError::PairCountOverflow { catalog_len })?;
    if pairs > limits.max_pairs {
        return Err(CatalogAtlasError::PairLimit {
            requested: pairs,
            limit: limits.max_pairs,
        });
    }
    let cells = pairs
        .checked_mul(degrees)
        .ok_or(CatalogAtlasError::ExtCellCountOverflow { pairs, degrees })?;
    if cells > limits.max_ext_cells {
        return Err(CatalogAtlasError::ExtCellLimit {
            requested: cells,
            limit: limits.max_ext_cells,
        });
    }
    let terms_per_source =
        degrees
            .checked_add(1)
            .ok_or(CatalogAtlasError::ResolutionTermOverflow {
                terms_per_source: degrees,
            })?;
    let resolution_terms = catalog_len.checked_mul(terms_per_source).ok_or(
        CatalogAtlasError::ResolutionCountOverflow {
            sources: catalog_len,
            terms_per_source,
        },
    )?;
    if resolution_terms > limits.max_resolution_terms {
        return Err(CatalogAtlasError::ResolutionTermLimit {
            requested: resolution_terms,
            limit: limits.max_resolution_terms,
        });
    }
    Ok((pairs, cells, (catalog_len, resolution_terms)))
}

fn build_resolutions(
    catalog: &IndecomposableCatalog,
    max_degree: usize,
    terms: (usize, usize),
    limits: CatalogAtlasLimits,
) -> Result<Vec<Arc<ProjectiveResolution>>, CatalogAtlasError> {
    let steps = max_degree
        .checked_add(1)
        .expect("preflight checks the degree successor");
    let mut resolutions = Vec::with_capacity(terms.0);
    let mut used = 0usize;
    for entry in catalog.entries() {
        let resolution = Arc::new(resolve(entry.module(), steps));
        used = used
            .checked_add(resolution.terms.len())
            .expect("preflight bounds the retained resolution terms");
        if used > limits.max_resolution_terms {
            return Err(CatalogAtlasError::ResolutionTermLimit {
                requested: used,
                limit: limits.max_resolution_terms,
            });
        }
        resolutions.push(resolution);
    }
    Ok(resolutions)
}

fn build_table(
    catalog: &IndecomposableCatalog,
    resolutions: &[Arc<ProjectiveResolution>],
    max_degree: usize,
    pairs: usize,
) -> CatalogExtTable {
    let mut rows = Vec::with_capacity(pairs);
    for (source, resolution) in resolutions.iter().enumerate() {
        for (target, entry) in catalog.entries().iter().enumerate() {
            let dimensions = ext_table_from_resolution(resolution, entry.module(), max_degree);
            rows.push(CatalogExtRow::new(source, target, dimensions));
        }
    }
    CatalogExtTable::new(catalog.len(), max_degree, rows)
}

fn checked_summand_count(
    multiplicities: &[usize],
    limit: usize,
) -> Result<usize, AtlasMaterializeError> {
    let mut count = 0usize;
    for &multiplicity in multiplicities {
        count = count
            .checked_add(multiplicity)
            .ok_or(AtlasMaterializeError::SummandCountOverflow)?;
        if count > limit {
            return Err(AtlasMaterializeError::SummandLimit {
                requested: count,
                limit,
            });
        }
    }
    Ok(count)
}

fn expand_modules<'a>(
    catalog: &'a IndecomposableCatalog,
    multiplicities: &[usize],
    count: usize,
) -> Result<Vec<&'a Module>, AtlasMaterializeError> {
    let mut modules = Vec::new();
    modules
        .try_reserve(count)
        .map_err(|_| AtlasMaterializeError::AllocationFailed { requested: count })?;
    for (index, &multiplicity) in multiplicities.iter().enumerate() {
        modules.extend(std::iter::repeat_n(
            catalog.entries()[index].module(),
            multiplicity,
        ));
    }
    Ok(modules)
}

fn add_entry_dimensions(
    dimensions: &mut [usize],
    index: usize,
    multiplicity: usize,
    entry_dimensions: &[usize],
) -> Result<(), AtlasMaterializeError> {
    for (vertex, &dimension) in entry_dimensions.iter().enumerate() {
        let product = multiplicity.checked_mul(dimension).ok_or(
            AtlasMaterializeError::DimensionProductOverflow {
                index,
                vertex,
                multiplicity,
                dimension,
            },
        )?;
        dimensions[vertex] = dimensions[vertex]
            .checked_add(product)
            .ok_or(AtlasMaterializeError::DimensionSumOverflow { vertex })?;
    }
    Ok(())
}

fn check_total_dimension(dimensions: &[usize]) -> Result<(), AtlasMaterializeError> {
    let mut total = 0usize;
    for &dimension in dimensions {
        total = total
            .checked_add(dimension)
            .ok_or(AtlasMaterializeError::TotalDimensionOverflow)?;
    }
    Ok(())
}

fn materialized_cell_count(
    algebra: &Algebra,
    dimensions: &[usize],
) -> Result<usize, AtlasMaterializeError> {
    // `Module::new` allocates each relation accumulator, term identity, and
    // product in sequence. Their cumulative cells bound temporary storage.
    let mut cells = 0usize;
    add_arrow_cells(&mut cells, algebra, dimensions)?;
    add_relation_cells(&mut cells, algebra, dimensions)?;
    Ok(cells)
}

fn add_arrow_cells(
    total: &mut usize,
    algebra: &Algebra,
    dimensions: &[usize],
) -> Result<(), AtlasMaterializeError> {
    let quiver = algebra.quiver();
    for index in 0..quiver.num_arrows() {
        let arrow = ArrowId(index as u32);
        add_cells(
            total,
            dimensions[quiver.source(arrow) as usize],
            dimensions[quiver.target(arrow) as usize],
        )?;
    }
    Ok(())
}

fn add_relation_cells(
    total: &mut usize,
    algebra: &Algebra,
    dimensions: &[usize],
) -> Result<(), AtlasMaterializeError> {
    let quiver = algebra.quiver();
    for relation in algebra.relations() {
        let source = relation.source() as usize;
        let target = relation.target() as usize;
        add_cells(total, dimensions[source], dimensions[target])?;
        for (_, word) in relation.terms() {
            let source_dimension = dimensions[word.source() as usize];
            add_cells(total, source_dimension, source_dimension)?;
            for &arrow in word.arrows() {
                add_cells(
                    total,
                    source_dimension,
                    dimensions[quiver.target(arrow) as usize],
                )?;
            }
        }
    }
    Ok(())
}

fn add_cells(total: &mut usize, rows: usize, columns: usize) -> Result<(), AtlasMaterializeError> {
    let cells = rows
        .checked_mul(columns)
        .ok_or(AtlasMaterializeError::CellProductOverflow { rows, columns })?;
    *total = total
        .checked_add(cells)
        .ok_or(AtlasMaterializeError::CellCountOverflow)?;
    Ok(())
}

fn materialized_sum(algebra: &Arc<Algebra>, modules: &[&Module], dimensions: Vec<usize>) -> Module {
    let quiver = algebra.quiver();
    let maps = (0..quiver.num_arrows())
        .map(|index| {
            let arrow = ArrowId(index as u32);
            let source = quiver.source(arrow) as usize;
            let target = quiver.target(arrow) as usize;
            let mut map = DenseMat::zero(dimensions[source], dimensions[target]);
            let mut source_offset = 0usize;
            let mut target_offset = 0usize;
            for module in modules {
                let block = module.map(arrow);
                for row in 0..block.rows() {
                    for column in 0..block.cols() {
                        map.set(
                            source_offset + row,
                            target_offset + column,
                            block.get(row, column),
                        );
                    }
                }
                source_offset += block.rows();
                target_offset += block.cols();
            }
            map
        })
        .collect();
    Module::new(algebra.clone(), dimensions, maps).expect("a direct sum of modules is a module")
}
