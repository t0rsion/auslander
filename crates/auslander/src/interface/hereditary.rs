use std::sync::Arc;

use crate::ext::ExtSpace;
use crate::family::CompiledModuleFamily;
use crate::field::Fp;

use super::{
    InterfaceFamilyHom, InterfaceFamilyHomError, InterfaceFamilyHomPlan, InterfaceFamilyHomWork,
    InterfacePartition,
};

/// A rejected fixed-interior hereditary Hom and Ext plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterfaceFamilyHereditaryError {
    /// The underlying fixed-interior Hom plan was rejected.
    Hom(InterfaceFamilyHomError),
    /// The algebra has a nonzero relation ideal, so the hereditary formula
    /// does not apply.
    NonzeroIdeal { basis_relations: usize },
}

display_error! { InterfaceFamilyHereditaryError {
    Self::Hom(error) => "fixed-interior Hom plan rejected: {error}";
    Self::NonzeroIdeal { basis_relations } => "hereditary interface plan needs the zero ideal, but the reduced basis has {basis_relations} relations";
} }

error_source! { InterfaceFamilyHereditaryError {
    Self::Hom(error) => Some(error),
    _ => None,
} }

impl From<InterfaceFamilyHomError> for InterfaceFamilyHereditaryError {
    fn from(error: InterfaceFamilyHomError) -> Self {
        Self::Hom(error)
    }
}

/// A fixed-interior plan for Hom and every Ext degree over a path algebra.
///
/// For a finite-dimensional path algebra, the standard projective resolution
/// has length one. Its first differential is the commuting-square matrix.
/// If that matrix is `[C; D]`, then
///
/// `rank [C; D] = rank C + rank(D_J K_Jᵀ)`,
///
/// where `K` is the canonical kernel basis of `C`. The wrapped Hom plan
/// computes the second rank for each fiber pair.
#[derive(Clone)]
pub struct InterfaceFamilyHereditaryPlan {
    hom: InterfaceFamilyHomPlan,
    arrow_cochains: usize,
}

impl InterfaceFamilyHereditaryPlan {
    /// Compiles one hereditary plan after checking that the relation ideal is
    /// zero.
    pub fn compile(
        family: &CompiledModuleFamily,
        partition: &InterfacePartition,
        anchor_values: &[Fp],
    ) -> Result<Self, InterfaceFamilyHereditaryError> {
        if !Arc::ptr_eq(family.algebra(), partition.algebra()) {
            return Err(InterfaceFamilyHereditaryError::Hom(
                InterfaceFamilyHomError::DifferentAlgebra,
            ));
        }
        let basis_relations = family.algebra().certificate().basis.len();
        if basis_relations != 0 {
            return Err(InterfaceFamilyHereditaryError::NonzeroIdeal { basis_relations });
        }
        let hom = InterfaceFamilyHomPlan::compile(family, partition, anchor_values)?;
        Ok(Self {
            arrow_cochains: family.hom_equations().len(),
            hom,
        })
    }

    accessor_methods! {
        /// The fixed-interior Hom plan used by this calculation.
        pub hom_plan() -> &InterfaceFamilyHomPlan = |this| &this.hom;
        /// The dimension of the arrow-cochain space in the standard resolution.
        pub arrow_cochains() -> usize = |this| this.arrow_cochains;
    }

    /// Computes exact Hom and Ext dimensions for two family fibers.
    pub fn compute(
        &self,
        source_values: &[Fp],
        target_values: &[Fp],
    ) -> Result<InterfaceFamilyHereditaryPair, InterfaceFamilyHereditaryError> {
        let hom = self.hom.compute(source_values, target_values)?;
        Ok(self.finish(hom))
    }

    /// Rebuilds the wrapped plan and checks the hereditary hypothesis.
    pub fn verify(&self) -> bool {
        self.hom.verify()
            && self.hom.family().algebra().certificate().basis.is_empty()
            && self.arrow_cochains == self.hom.family().hom_equations().len()
    }

    fn finish(&self, hom: InterfaceFamilyHom) -> InterfaceFamilyHereditaryPair {
        let hom_work = hom.work();
        let constraint_rank = hom_work
            .fixed_rank
            .checked_add(hom_work.interface_rank)
            .expect("two ranks bounded by one equation matrix cannot overflow");
        let ext1_dimension = self
            .arrow_cochains
            .checked_sub(constraint_rank)
            .expect("the constraint rank cannot exceed its arrow-cochain rows");
        InterfaceFamilyHereditaryPair {
            plan: self.clone(),
            hom,
            ext1_dimension,
            work: InterfaceFamilyHereditaryWork {
                hom: hom_work,
                arrow_cochains: self.arrow_cochains,
                constraint_rank,
            },
        }
    }
}

debug_fields! { InterfaceFamilyHereditaryPlan |this| {
    "hom_plan" => this.hom;
    "arrow_cochains" => this.arrow_cochains;
} }

/// Exact work counts for one hereditary fixed-interior pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InterfaceFamilyHereditaryWork {
    /// Fixed-interior Hom work, including both rank terms.
    pub hom: InterfaceFamilyHomWork,
    /// Dimension of the arrow-cochain space.
    pub arrow_cochains: usize,
    /// Rank of the full standard-resolution differential.
    pub constraint_rank: usize,
}

/// Exact Hom and Ext dimensions for one hereditary family pair.
#[derive(Clone)]
pub struct InterfaceFamilyHereditaryPair {
    plan: InterfaceFamilyHereditaryPlan,
    hom: InterfaceFamilyHom,
    ext1_dimension: usize,
    work: InterfaceFamilyHereditaryWork,
}

impl InterfaceFamilyHereditaryPair {
    accessor_methods! {
        /// The compiled hereditary plan.
        pub plan() -> &InterfaceFamilyHereditaryPlan = |this| &this.plan;
        /// The lifted canonical Hom space.
        pub hom() -> &InterfaceFamilyHom = |this| &this.hom;
        /// `dim_k Hom(source, target)`.
        pub hom_dimension() -> usize = |this| this.hom.dim();
        /// `dim_k Ext^1(source, target)`.
        pub ext1_dimension() -> usize = |this| this.ext1_dimension;
        /// Exact fixed and per-fiber work counts.
        pub work() -> InterfaceFamilyHereditaryWork = |this| this.work;
    }

    /// Returns the exact Ext dimension. Degree zero is Hom, degree one uses
    /// the standard resolution, and every higher degree vanishes.
    pub fn ext_dimension(&self, degree: usize) -> usize {
        match degree {
            0 => self.hom_dimension(),
            1 => self.ext1_dimension,
            _ => 0,
        }
    }

    /// Recomputes Hom and the first two Ext groups through the generic path.
    pub fn verify(&self) -> bool {
        if !self.plan.verify() || !self.hom.verify() {
            return false;
        }
        let source = self.hom.source();
        let target = self.hom.target();
        let Ok(ext1) = ExtSpace::new(source, target, 1) else {
            return false;
        };
        let Ok(ext2) = ExtSpace::new(source, target, 2) else {
            return false;
        };
        ext1.dim() == self.ext1_dimension && ext2.dim() == 0
    }
}

debug_fields! { InterfaceFamilyHereditaryPair |this| {
    "source_dimensions" => this.hom.source().dim_vector();
    "target_dimensions" => this.hom.target().dim_vector();
    "hom_dimension" => this.hom_dimension();
    "ext1_dimension" => this.ext1_dimension;
    "work" => this.work;
} }
