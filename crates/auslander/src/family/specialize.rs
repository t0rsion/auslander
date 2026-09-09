use std::collections::BTreeMap;
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::field::{Fp, PrimeField};
use crate::hom::matrix_is_zero;
use crate::homspace::HomSpace;
use crate::linalg::{DenseMat, SparseMat, SparseRow};
use crate::module::Module;

use super::layout::checked_coordinate;
use super::metadata::{hom_layout, relation_layouts};
use super::types::{
    CompiledModuleFamily, FamilyError, FamilyFixedEntry, FamilyLayout, FamilyParameter,
    FamilyParameterPosition,
};

impl CompiledModuleFamily {
    /// Compiles a fixed algebra, dimension vector, and coordinate pattern.
    pub fn new(
        algebra: &Arc<Algebra>,
        dimensions: Vec<usize>,
        fixed: Vec<FamilyFixedEntry>,
        parameters: Vec<FamilyParameter>,
    ) -> Result<Self, FamilyError> {
        let layout = FamilyLayout::new(algebra, dimensions)?;
        let fixed = checked_fixed(&layout, algebra, fixed)?;
        let (parameters, parameter_indices) = checked_parameters(&layout, &fixed, parameters)?;
        let relation_evaluations = relation_layouts(algebra, &layout)?;
        let hom_equations = hom_layout(&layout)?;
        Ok(Self {
            algebra: algebra.clone(),
            layout,
            fixed,
            parameters,
            parameter_indices,
            relation_evaluations,
            hom_equations,
        })
    }

    /// Compiles a family with the same checks as [`Self::new`].
    pub fn compile(
        algebra: &Arc<Algebra>,
        dimensions: Vec<usize>,
        fixed: Vec<FamilyFixedEntry>,
        parameters: Vec<FamilyParameter>,
    ) -> Result<Self, FamilyError> {
        Self::new(algebra, dimensions, fixed, parameters)
    }

    accessor_methods! {
        /// The fixed algebra shared by every specialization.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The fixed dimensions and coordinate layout.
        pub layout() -> &FamilyLayout = |this| &this.layout;
        /// Fixed entries in specification order.
        pub fixed_entries() -> &[FamilyFixedEntry] = |this| &this.fixed;
        /// Named parameters in specialization order.
        pub parameters() -> &[FamilyParameterPosition] = |this| &this.parameters;
        /// Structural relation evaluation layouts.
        pub relation_evaluations() -> &[super::types::RelationEvaluationLayout] = |this| &this.relation_evaluations;
        /// Structural commuting-square layouts for Hom equations.
        pub hom_equations() -> &[super::types::HomEquationLayout] = |this| &this.hom_equations;
    }

    /// Returns the parameter index for `name`.
    pub fn parameter_index(&self, name: &str) -> Option<usize> {
        self.parameter_indices.get(name).copied()
    }

    /// Fills the family coordinates and checks its compiled relation plan.
    ///
    /// Each plan stores the coefficient and arrow sequence of one reduced
    /// relation term. Its left-to-right matrix product is the action checked
    /// by [`Module::new`]. The fixed layout proves map counts and shapes.
    pub fn specialize(&self, values: &[Fp]) -> Result<Module, FamilyError> {
        let maps = self.specialized_maps(values)?;
        check_relations(self, &maps)?;
        Ok(Module::from_relation_checked(
            self.algebra.clone(),
            self.layout.dimensions.clone(),
            maps,
        ))
    }

    /// Fills the family and checks it through the generic module constructor.
    pub fn specialize_generic(&self, values: &[Fp]) -> Result<Module, FamilyError> {
        let maps = self.specialized_maps(values)?;
        Module::new(self.algebra.clone(), self.layout.dimensions.clone(), maps).map_err(Into::into)
    }

    fn specialized_maps(&self, values: &[Fp]) -> Result<Vec<DenseMat>, FamilyError> {
        let field = self.algebra.field();
        let values = checked_parameter_values(&self.parameters, values, &field)?;
        let coordinates =
            filled_coordinates(&self.layout, &self.fixed, &self.parameters, &values, &field)?;
        filled_maps(&self.layout, &coordinates)
    }

    /// Fills the family from raw canonical values in parameter order.
    pub fn specialize_raw(&self, values: &[u64]) -> Result<Module, FamilyError> {
        let field = self.algebra.field();
        let canonical = raw_parameter_values(values, &field)?;
        self.specialize(&canonical)
    }

    /// Specializes two fibers and solves their compiled Hom equations.
    ///
    /// The equation plan stores the same variable order and commuting-square
    /// coefficients as [`HomSpace::new`]. Debug builds compare the exact basis.
    pub fn hom_space(
        &self,
        source_values: &[Fp],
        target_values: &[Fp],
    ) -> Result<HomSpace, FamilyError> {
        let source = self.specialize(source_values)?;
        let target = self.specialize(target_values)?;
        Ok(compiled_hom_space(self, &source, &target))
    }

    /// Specializes two fibers and uses the generic Hom constructor.
    pub fn hom_space_generic(
        &self,
        source_values: &[Fp],
        target_values: &[Fp],
    ) -> Result<HomSpace, FamilyError> {
        let source = self.specialize_generic(source_values)?;
        let target = self.specialize_generic(target_values)?;
        Ok(HomSpace::new(&source, &target)
            .expect("two fibers of one compiled family share their algebra"))
    }

    /// Recompiles the fixed pattern and compares every structural layout.
    pub fn verify(&self) -> bool {
        let parameters = self
            .parameters
            .iter()
            .map(|parameter| {
                let coordinate = parameter.coordinate;
                FamilyParameter::new(
                    parameter.name.clone(),
                    coordinate.arrow,
                    coordinate.row,
                    coordinate.column,
                )
            })
            .collect();
        let Ok(rebuilt) = Self::new(
            &self.algebra,
            self.layout.dimensions.clone(),
            self.fixed.clone(),
            parameters,
        ) else {
            return false;
        };
        Arc::ptr_eq(&self.algebra, &rebuilt.algebra)
            && self.layout == rebuilt.layout
            && self.fixed == rebuilt.fixed
            && self.parameters == rebuilt.parameters
            && self.parameter_indices == rebuilt.parameter_indices
            && self.relation_evaluations == rebuilt.relation_evaluations
            && self.hom_equations == rebuilt.hom_equations
    }
}

fn compiled_hom_space(family: &CompiledModuleFamily, source: &Module, target: &Module) -> HomSpace {
    let field = family.algebra.field();
    let mut rows = Vec::new();
    for equation in &family.hom_equations {
        let entries = equation
            .terms
            .iter()
            .map(|term| {
                let coordinate = term.coefficient;
                let map = match term.side {
                    super::types::HomCoefficientSide::Target => target.map(coordinate.arrow),
                    super::types::HomCoefficientSide::Source => source.map(coordinate.arrow),
                };
                let value = map.get(coordinate.row, coordinate.column);
                let value = match term.side {
                    super::types::HomCoefficientSide::Target => value,
                    super::types::HomCoefficientSide::Source => field.neg(value),
                };
                (term.variable.index, value)
            })
            .collect();
        let row = SparseRow::from_entries(entries, &field);
        if !row.is_zero() {
            rows.push(row);
        }
    }
    let constraints = SparseMat::from_rows(rows, family.layout.hom_variable_count);
    let flat = constraints.kernel_basis(&field).to_dense();
    HomSpace::from_checked_flat(source, target, flat)
}

fn check_relations(family: &CompiledModuleFamily, maps: &[DenseMat]) -> Result<(), FamilyError> {
    let field = family.algebra.field();
    for relation in &family.relation_evaluations {
        let mut value = DenseMat::zero(relation.rows, relation.columns);
        for term in &relation.terms {
            let mut action = DenseMat::identity(relation.rows);
            for factor in &term.factors {
                action = action.mul(&maps[factor.arrow.index()], &field);
            }
            value.add_scaled_assign(&action, term.coefficient, &field);
        }
        if !matrix_is_zero(&value) {
            return Err(FamilyError::Module(
                crate::module::ModuleError::RelationActsNonzero {
                    index: relation.relation,
                },
            ));
        }
    }
    Ok(())
}

fn checked_parameter_values(
    parameters: &[FamilyParameterPosition],
    values: &[Fp],
    field: &PrimeField,
) -> Result<Vec<Fp>, FamilyError> {
    if values.len() != parameters.len() {
        return Err(FamilyError::ParameterCountMismatch {
            expected: parameters.len(),
            got: values.len(),
        });
    }
    for (index, &value) in values.iter().enumerate() {
        if value.raw() >= field.modulus() {
            return Err(FamilyError::NonCanonicalParameterValue {
                index,
                value: value.raw(),
            });
        }
    }
    Ok(values.to_vec())
}

fn raw_parameter_values(values: &[u64], field: &PrimeField) -> Result<Vec<Fp>, FamilyError> {
    let mut canonical = Vec::new();
    canonical
        .try_reserve(values.len())
        .map_err(|_| FamilyError::CoordinateAllocationFailed {
            coordinates: values.len(),
        })?;
    for &value in values {
        if value >= field.modulus() {
            return Err(FamilyError::NonCanonicalParameterValue {
                index: canonical.len(),
                value,
            });
        }
        canonical.push(field.elem(value as i64));
    }
    Ok(canonical)
}

fn filled_coordinates(
    layout: &FamilyLayout,
    fixed: &[FamilyFixedEntry],
    parameters: &[FamilyParameterPosition],
    values: &[Fp],
    field: &PrimeField,
) -> Result<Vec<Fp>, FamilyError> {
    let count = layout.coordinate_count();
    let mut coordinates = Vec::new();
    coordinates
        .try_reserve(count)
        .map_err(|_| FamilyError::CoordinateAllocationFailed { coordinates: count })?;
    coordinates.resize(count, field.zero());
    for entry in fixed {
        let coordinate = layout
            .coordinate(entry.arrow, entry.row, entry.column)
            .expect("compiled fixed coordinate is in the layout");
        coordinates[coordinate.index] = entry.value;
    }
    for (index, parameter) in parameters.iter().enumerate() {
        coordinates[parameter.coordinate.index] = values[index];
    }
    Ok(coordinates)
}

fn filled_maps(layout: &FamilyLayout, coordinates: &[Fp]) -> Result<Vec<DenseMat>, FamilyError> {
    let mut maps = Vec::new();
    maps.try_reserve(layout.arrows.len())
        .map_err(|_| FamilyError::CoordinateAllocationFailed {
            coordinates: layout.arrows.len(),
        })?;
    for arrow in &layout.arrows {
        maps.push(filled_map(layout, arrow, coordinates));
    }
    Ok(maps)
}

fn filled_map(
    layout: &FamilyLayout,
    arrow: &super::types::FamilyArrowLayout,
    coordinates: &[Fp],
) -> DenseMat {
    let mut map = DenseMat::zero(arrow.rows, arrow.columns);
    for row in 0..arrow.rows {
        for column in 0..arrow.columns {
            let coordinate = layout
                .coordinate(arrow.arrow, row, column)
                .expect("arrow layout coordinate exists");
            map.set(row, column, coordinates[coordinate.index]);
        }
    }
    map
}

fn checked_fixed(
    layout: &FamilyLayout,
    algebra: &Algebra,
    entries: Vec<FamilyFixedEntry>,
) -> Result<Vec<FamilyFixedEntry>, FamilyError> {
    let mut seen = BTreeMap::new();
    for entry in &entries {
        checked_coordinate(layout, entry.arrow, entry.row, entry.column)?;
        if entry.value.raw() >= algebra.field().modulus() {
            return Err(FamilyError::NonCanonicalFixedValue {
                arrow: entry.arrow,
                row: entry.row,
                column: entry.column,
                value: entry.value.raw(),
            });
        }
        let coordinate = (entry.arrow, entry.row, entry.column);
        if seen.insert(coordinate, ()).is_some() {
            return Err(FamilyError::DuplicateFixedCoordinate {
                arrow: entry.arrow,
                row: entry.row,
                column: entry.column,
            });
        }
    }
    Ok(entries)
}

fn checked_parameters(
    layout: &FamilyLayout,
    fixed: &[FamilyFixedEntry],
    entries: Vec<FamilyParameter>,
) -> Result<(Vec<FamilyParameterPosition>, BTreeMap<String, usize>), FamilyError> {
    let mut names = BTreeMap::new();
    let fixed_coordinates: BTreeMap<_, _> = fixed
        .iter()
        .map(|entry| ((entry.arrow, entry.row, entry.column), ()))
        .collect();
    let mut coordinates = BTreeMap::new();
    let mut positions = Vec::new();
    positions
        .try_reserve(entries.len())
        .map_err(|_| FamilyError::CoordinateAllocationFailed {
            coordinates: entries.len(),
        })?;
    for (index, parameter) in entries.into_iter().enumerate() {
        if parameter.name.is_empty() {
            return Err(FamilyError::EmptyParameterName);
        }
        if names.insert(parameter.name.clone(), index).is_some() {
            return Err(FamilyError::DuplicateParameterName {
                name: parameter.name,
            });
        }
        let coordinate =
            checked_coordinate(layout, parameter.arrow, parameter.row, parameter.column)?;
        let key = (parameter.arrow, parameter.row, parameter.column);
        if fixed_coordinates.contains_key(&key) {
            return Err(FamilyError::FixedParameterCollision {
                arrow: parameter.arrow,
                row: parameter.row,
                column: parameter.column,
            });
        }
        if coordinates.insert(key, ()).is_some() {
            return Err(FamilyError::DuplicateParameterCoordinate {
                arrow: parameter.arrow,
                row: parameter.row,
                column: parameter.column,
            });
        }
        positions.push(FamilyParameterPosition {
            name: parameter.name,
            coordinate,
            index,
        });
    }
    Ok((positions, names))
}
