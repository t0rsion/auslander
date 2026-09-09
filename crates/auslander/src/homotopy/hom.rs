//! Chain Hom spaces and homotopy quotients.

use crate::complex::CheckedComplex;
use crate::field::Fp;
use crate::homspace::{HomSpace, deterministic_complement, row_times, scale_morphism, stack_rows};
use crate::linalg::DenseMat;

use super::chain::{
    ChainHomotopy, ChainMap, ChainMapError, agrees_after_padding, checked_union_range, padded_pair,
    rebase_morphism, same_complex_data, shifted_complex,
};
use super::complex::{BoundedComplex, BoundedComplexError, zero_between};

/// A deterministic basis of chain maps between two bounded complexes.
#[derive(Clone, Debug)]
pub struct ChainHomSpace {
    source: BoundedComplex,
    target: BoundedComplex,
    components: Vec<HomSpace>,
    flat: DenseMat,
}

fn chain_flat(map: &ChainMap, spaces: &[HomSpace]) -> Vec<Fp> {
    let mut row = Vec::with_capacity(spaces.iter().map(HomSpace::dim).sum());
    for (component, space) in map.components.iter().zip(spaces) {
        let component = if component.source().ptr_eq(space.source())
            && component.target().ptr_eq(space.target())
        {
            component.clone()
        } else {
            rebase_morphism(component, space.source(), space.target())
        };
        row.extend(
            space
                .coords(&component)
                .expect("chain map component has matching endpoints"),
        );
    }
    row
}

fn chain_map_from_flat(
    source: &BoundedComplex,
    target: &BoundedComplex,
    spaces: &[HomSpace],
    row: &[Fp],
) -> ChainMap {
    let mut components = Vec::with_capacity(spaces.len());
    let mut offset = 0;
    for space in spaces {
        let end = offset + space.dim();
        components.push(space.morphism(&row[offset..end]));
        offset = end;
    }
    ChainMap::new(source, target, components)
        .expect("chain Hom kernel rows satisfy the chain equations")
}

fn chain_constraints(
    source: &BoundedComplex,
    target: &BoundedComplex,
    spaces: &[HomSpace],
) -> DenseMat {
    let width: usize = spaces.iter().map(HomSpace::dim).sum();
    let mut offsets = Vec::with_capacity(spaces.len());
    let mut cursor = 0;
    for space in spaces {
        offsets.push(cursor);
        cursor += space.dim();
    }
    let mut rows: Vec<Vec<Fp>> = Vec::new();
    for index in 1..source.len() {
        let equation = HomSpace::new(&source.terms[index], &target.terms[index - 1])
            .expect("chain equation endpoints share the algebra");
        let equation_dim = equation.dim();
        let mut contributions: Vec<Vec<Fp>> =
            vec![vec![source.terms[0].field().zero(); width]; equation_dim];
        for (variable_index, space) in spaces.iter().enumerate() {
            for basis_index in 0..space.dim() {
                let basis = space.basis_morphism(basis_index);
                let contribution = if variable_index == index - 1 {
                    source.differentials[index - 1]
                        .then(&basis)
                        .expect("source differential and component endpoints match")
                } else if variable_index == index {
                    scale_morphism(
                        &basis
                            .then(&target.differentials[index - 1])
                            .expect("component and target differential endpoints match"),
                        source.terms[0].field().neg(source.terms[0].field().one()),
                    )
                } else {
                    continue;
                };
                let coordinates = equation
                    .coords(&contribution)
                    .expect("a composite of module morphisms lies in the equation Hom space");
                for (row, value) in coordinates.into_iter().enumerate() {
                    contributions[row][offsets[variable_index] + basis_index] = value;
                }
            }
        }
        rows.extend(contributions);
    }
    DenseMat::from_rows_with_cols(&rows, width)
}

fn homotopy_rows(
    source: &BoundedComplex,
    target: &BoundedComplex,
    spaces: &[HomSpace],
    ambient: &DenseMat,
) -> DenseMat {
    let field = source.terms[0].field();
    let mut rows = Vec::new();
    for index in 0..source.len().saturating_sub(1) {
        let space = HomSpace::new(&source.terms[index], &target.terms[index + 1])
            .expect("homotopy endpoints share the algebra");
        for basis_index in 0..space.dim() {
            let mut components = Vec::with_capacity(source.len().saturating_sub(1));
            for j in 0..source.len().saturating_sub(1) {
                let source_term = &source.terms[j];
                let target_term = &target.terms[j + 1];
                components.push(if j == index {
                    space.basis_morphism(basis_index)
                } else {
                    zero_between(source_term, target_term)
                });
            }
            let homotopy = ChainHomotopy::new(source, target, components)
                .expect("homotopy basis components have matching endpoints");
            let boundary = homotopy
                .boundary()
                .expect("homotopy boundary is a chain map");
            rows.push(chain_flat(&boundary, spaces));
        }
    }
    let inner = DenseMat::from_rows_with_cols(&rows, ambient.cols());
    inner.row_space_basis(&field)
}

impl ChainHomSpace {
    /// Builds the chain-map Hom space by solving the chain equations.
    pub fn new(
        source: &BoundedComplex,
        target: &BoundedComplex,
    ) -> Result<ChainHomSpace, ChainMapError> {
        let range = checked_union_range(source, target)?;
        let (source, target) = padded_pair(source, target, range)?;
        let components: Vec<HomSpace> = source
            .terms
            .iter()
            .zip(&target.terms)
            .map(|(source, target)| HomSpace::new(source, target).expect("algebras were checked"))
            .collect();
        let constraints = chain_constraints(&source, &target, &components);
        let flat = constraints.kernel_basis(&source.terms[0].field());
        Ok(ChainHomSpace {
            source: source.clone(),
            target: target.clone(),
            components,
            flat,
        })
    }

    accessor_methods! {
        /// The source complex.
        pub source() -> &BoundedComplex = |this| &this.source;
        /// The target complex.
        pub target() -> &BoundedComplex = |this| &this.target;
        /// The dimension of the chain-map space.
        pub dim() -> usize = |this| this.flat.rows();
        /// The chain-map basis in deterministic kernel order.
        pub basis_rows() -> &DenseMat = |this| &this.flat;
    }

    /// The basis chain map at `index`.
    pub fn basis_morphism(&self, index: usize) -> ChainMap {
        chain_map_from_flat(
            &self.source,
            &self.target,
            &self.components,
            self.flat.row(index),
        )
    }

    /// All basis chain maps in deterministic order.
    pub fn basis_iter(&self) -> impl Iterator<Item = ChainMap> + '_ {
        (0..self.dim()).map(|index| self.basis_morphism(index))
    }

    /// Rebuilds a chain map from coordinates in the chain-map basis.
    pub fn morphism(&self, coordinates: &[Fp]) -> ChainMap {
        assert_eq!(coordinates.len(), self.dim());
        let row = row_times(coordinates, &self.flat, &self.source.terms[0].field());
        chain_map_from_flat(&self.source, &self.target, &self.components, &row)
    }

    /// Coordinates of a chain map in the deterministic basis.
    pub fn coords(&self, map: &ChainMap) -> Result<Vec<Fp>, ChainMapError> {
        if !same_complex_data(&self.source, &map.source)
            || !same_complex_data(&self.target, &map.target)
        {
            return Err(ChainMapError::OutsideHomSpace);
        }
        let row = chain_flat(map, &self.components);
        self.flat
            .transpose()
            .solve(&row, &self.source.terms[0].field())
            .ok_or(ChainMapError::OutsideHomSpace)
    }

    /// Recomputes the chain-map equations and compares their deterministic basis.
    pub fn verify(&self) -> bool {
        let Ok(rebuilt) = ChainHomSpace::new(&self.source, &self.target) else {
            return false;
        };
        rebuilt.flat == self.flat
    }

    /// The quotient by null-homotopic chain maps.
    pub fn quotient(&self) -> Result<ChainHomQuotient, ChainMapError> {
        let null = homotopy_rows(&self.source, &self.target, &self.components, &self.flat);
        for row in 0..null.rows() {
            if self
                .flat
                .transpose()
                .solve(null.row(row), &self.source.terms[0].field())
                .is_none()
            {
                return Err(ChainMapError::OutsideHomSpace);
            }
        }
        let complement = deterministic_complement(&self.flat, &null, &self.source.terms[0].field());
        Ok(ChainHomQuotient {
            space: self.clone(),
            null,
            complement,
        })
    }
}

impl CheckedComplex {
    /// Converts a display-order checked complex to homological degree order.
    pub fn bounded(&self, lower: i32) -> Result<BoundedComplex, BoundedComplexError> {
        BoundedComplex::from_checked(self, lower)
    }
}

/// Hom chain maps modulo null-homotopic maps.
#[derive(Clone, Debug)]
pub struct ChainHomQuotient {
    space: ChainHomSpace,
    null: DenseMat,
    complement: DenseMat,
}

impl ChainHomQuotient {
    accessor_methods! {
        /// The source complex.
        pub source() -> &BoundedComplex = |this| this.space.source();
        /// The target complex.
        pub target() -> &BoundedComplex = |this| this.space.target();
        /// The quotient dimension.
        pub dim() -> usize = |this| this.complement.rows();
        /// The null-homotopic subspace in component coordinates.
        pub null_homotopic_basis() -> &DenseMat = |this| &this.null;
        /// The deterministic quotient complement in component coordinates.
        pub complement_basis() -> &DenseMat = |this| &this.complement;
    }

    /// Recomputes the ambient space, null-homotopic subspace, and complement.
    pub fn verify(&self) -> bool {
        self.space.verify()
            && self.space.quotient().is_ok_and(|rebuilt| {
                rebuilt.null == self.null && rebuilt.complement == self.complement
            })
    }

    /// Rebuilds a quotient representative from complement coordinates.
    pub fn representative(&self, coordinates: &[Fp]) -> ChainMap {
        assert_eq!(coordinates.len(), self.dim());
        let row = row_times(
            coordinates,
            &self.complement,
            &self.space.source.terms[0].field(),
        );
        chain_map_from_flat(
            &self.space.source,
            &self.space.target,
            &self.space.components,
            &row,
        )
    }

    /// Reduces a chain map to quotient coordinates and a null-homotopic remainder.
    pub fn reduce(&self, map: &ChainMap) -> Result<(Vec<Fp>, ChainMap), ChainMapError> {
        if !same_complex_data(&self.space.source, &map.source)
            || !same_complex_data(&self.space.target, &map.target)
        {
            return Err(ChainMapError::OutsideHomSpace);
        }
        let field = self.space.source.terms[0].field();
        let row = chain_flat(map, &self.space.components);
        let stacked = stack_rows(&[&self.complement, &self.null], self.complement.cols());
        let Some(coordinates) = stacked.transpose().solve(&row, &field) else {
            return Err(ChainMapError::OutsideHomSpace);
        };
        let quotient_coordinates = coordinates[..self.complement.rows()].to_vec();
        let null_row = row_times(&coordinates[self.complement.rows()..], &self.null, &field);
        Ok((
            quotient_coordinates,
            chain_map_from_flat(
                &self.space.source,
                &self.space.target,
                &self.space.components,
                &null_row,
            ),
        ))
    }
}

/// The degree-`q` chain Hom space obtained from `target.shift(q)`.
#[derive(Clone, Debug)]
pub struct HomotopyHom {
    degree: i32,
    source: BoundedComplex,
    target: BoundedComplex,
    shifted_target: BoundedComplex,
    space: ChainHomSpace,
}

impl HomotopyHom {
    /// Builds degree-`q` chain maps and retains the unshifted target.
    pub fn new(
        source: &BoundedComplex,
        target: &BoundedComplex,
        degree: i32,
    ) -> Result<HomotopyHom, ChainMapError> {
        let shifted_target = shifted_complex(target, degree)?;
        let space = ChainHomSpace::new(source, &shifted_target)?;
        Ok(HomotopyHom {
            degree,
            source: source.clone(),
            target: target.clone(),
            shifted_target,
            space,
        })
    }

    accessor_methods! {
        /// The retained degree `q`.
        pub degree() -> i32 = |this| this.degree;
        /// The unshifted source complex.
        pub source() -> &BoundedComplex = |this| &this.source;
        /// The unshifted target complex.
        pub target() -> &BoundedComplex = |this| &this.target;
        /// The target complex used by the degree-zero chain-map solver.
        pub shifted_target() -> &BoundedComplex = |this| &this.shifted_target;
        /// The normalized degree-zero chain Hom space.
        pub chain_space() -> &ChainHomSpace = |this| &this.space;
        /// The dimension of the degree-`q` chain-map space.
        pub dim() -> usize = |this| this.space.dim();
        /// The deterministic cycle basis in component coordinates.
        pub basis_rows() -> &DenseMat = |this| this.space.basis_rows();
    }

    /// The basis degree-`q` chain map at `index`.
    pub fn basis_morphism(&self, index: usize) -> ChainMap {
        self.space.basis_morphism(index)
    }

    /// All basis degree-`q` chain maps in deterministic order.
    pub fn basis_iter(&self) -> impl Iterator<Item = ChainMap> + '_ {
        self.space.basis_iter()
    }

    /// Rebuilds a degree-`q` chain map from deterministic coordinates.
    pub fn morphism(&self, coordinates: &[Fp]) -> ChainMap {
        self.space.morphism(coordinates)
    }

    /// Coordinates of a degree-`q` chain map in the deterministic basis.
    pub fn coords(&self, map: &ChainMap) -> Result<Vec<Fp>, ChainMapError> {
        self.space.coords(map)
    }

    /// Recomputes the shift and cycle basis stored by this value.
    pub fn verify(&self) -> bool {
        let Ok(shifted_target) = shifted_complex(&self.target, self.degree) else {
            return false;
        };
        agrees_after_padding(&self.source, self.space.source())
            && self.shifted_target.agrees_with(&shifted_target)
            && agrees_after_padding(&self.shifted_target, self.space.target())
            && self.space.verify()
    }

    /// Returns the quotient by null-homotopic degree-`q` maps.
    pub fn quotient(&self) -> Result<HomotopyHomQuotient, ChainMapError> {
        Ok(HomotopyHomQuotient {
            hom: self.clone(),
            quotient: self.space.quotient()?,
        })
    }
}

/// Degree-`q` chain Hom modulo null-homotopic maps.
#[derive(Clone, Debug)]
pub struct HomotopyHomQuotient {
    hom: HomotopyHom,
    quotient: ChainHomQuotient,
}

impl HomotopyHomQuotient {
    accessor_methods! {
        /// The degree-`q` Hom value behind this quotient.
        pub hom() -> &HomotopyHom = |this| &this.hom;
        /// The retained degree `q`.
        pub degree() -> i32 = |this| this.hom.degree();
        /// The unshifted source complex.
        pub source() -> &BoundedComplex = |this| this.hom.source();
        /// The unshifted target complex.
        pub target() -> &BoundedComplex = |this| this.hom.target();
        /// The shifted target used by the chain-map solver.
        pub shifted_target() -> &BoundedComplex = |this| this.hom.shifted_target();
        /// The quotient dimension.
        pub dim() -> usize = |this| this.quotient.dim();
        /// The null-homotopic basis in component coordinates.
        pub null_homotopic_basis() -> &DenseMat = |this| this.quotient.null_homotopic_basis();
        /// The deterministic quotient complement in component coordinates.
        pub complement_basis() -> &DenseMat = |this| this.quotient.complement_basis();
    }

    /// Recomputes the shift, cycle basis, boundary basis, and complement.
    pub fn verify(&self) -> bool {
        self.hom.verify()
            && self.quotient.verify()
            && agrees_after_padding(self.hom.source(), self.quotient.source())
            && agrees_after_padding(self.hom.shifted_target(), self.quotient.target())
    }

    /// Rebuilds a quotient representative from complement coordinates.
    pub fn representative(&self, coordinates: &[Fp]) -> ChainMap {
        self.quotient.representative(coordinates)
    }

    /// Reduces a degree-`q` chain map to class coordinates and a null map.
    pub fn reduce(&self, map: &ChainMap) -> Result<(Vec<Fp>, ChainMap), ChainMapError> {
        self.quotient.reduce(map)
    }
}

impl ChainMap {
    /// Whether this map represents zero modulo chain homotopy.
    pub fn is_null_homotopic(&self) -> Result<bool, ChainMapError> {
        let quotient = ChainHomSpace::new(&self.source, &self.target)
            .map_err(|_| ChainMapError::OutsideHomSpace)?
            .quotient()?;
        Ok(quotient.reduce(self)?.0.iter().all(|x| x.is_zero()))
    }
}

/// A short name for the bounded homological complex type.
pub type DegreeComplex = BoundedComplex;

/// A short name for a chain homotopy.
pub type Homotopy = ChainHomotopy;
