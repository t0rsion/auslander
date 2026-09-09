use crate::basic::{AddClosureWitness, BasicDecomposition};
use crate::decompose::{Split, SplitError, add_morphisms, mutually_inverse};
use crate::hom::{HomError, Morphism, zero_morphism};
use crate::homotopy::{BoundedComplex, BoundedComplexError, ChainMap, ChainMapError, DegreeRange};
use crate::homspace::{HomSpace, HomSpaceError};
use crate::linalg::DenseMat;
use crate::module::{Module, ModuleError, same_representation};
use crate::target::VerifiedTargetPresentation;

/// Rejected strict transport input or a failed checked construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransportError {
    /// The supplied target presentation does not verify.
    InvalidTarget,
    /// A source term has no witness.
    SourceWitnessCount { expected: usize, got: usize },
    /// The source witness at `term` does not verify.
    InvalidSourceWitness { term: usize },
    /// The source witness at `term` belongs to another tilting module.
    SourceWitnessTarget { term: usize },
    /// The source witness at `term` belongs to another complex term.
    SourceWitnessTerm { term: usize },
    /// The target term at `term` is not projective.
    TargetTermNotProjective { term: usize },
    /// A stored target summand does not match one canonical projective.
    TargetSummandMatch { term: usize, summand: usize },
    /// A stored source summand does not match one target summand.
    SourceSummandMatch { term: usize, summand: usize },
    /// A required isomorphism was not certified.
    Isomorphism { reason: String },
    /// A split did not pass its defining identities.
    Split(SplitError),
    /// A module action or morphism failed its checked constructor.
    Module(ModuleError),
    /// A module morphism failed its checked constructor or composition.
    Hom(HomError),
    /// Coordinates did not belong to their deterministic Hom space.
    HomSpace(HomSpaceError),
    /// A bounded complex failed its checked constructor.
    Complex(BoundedComplexError),
    /// A chain map failed its checked constructor.
    Chain(ChainMapError),
    /// A chain map is not stored on the supplied source and target complexes.
    ChainDomain,
    /// A homotopy is not stored on the supplied source and target complexes.
    HomotopyDomain,
    /// A stored construction violated an internal invariant.
    Defect { reason: String },
}

display_error! { TransportError {
    Self::InvalidTarget => "target presentation does not verify";
    Self::SourceWitnessCount { expected, got } => "source complex has {got} witnesses, expected {expected}";
    Self::InvalidSourceWitness { term } => "source witness at term {term} does not verify";
    Self::SourceWitnessTarget { term } => "source witness at term {term} belongs to another tilting module";
    Self::SourceWitnessTerm { term } => "source witness at term {term} belongs to another complex term";
    Self::TargetTermNotProjective { term } => "target term {term} has no verified canonical-projective decomposition";
    Self::TargetSummandMatch { term, summand } => "target term {term} summand {summand} matches no canonical projective";
    Self::SourceSummandMatch { term, summand } => "source term {term} summand {summand} matches no target summand";
    Self::Isomorphism { reason } => "isomorphism was not certified: {reason}";
    Self::Split(error) => "split rejected: {error}";
    Self::Module(error) => "module rejected: {error}";
    Self::Hom(error) => "morphism rejected: {error}";
    Self::HomSpace(error) => "Hom-space coordinates rejected: {error}";
    Self::Complex(error) => "complex rejected: {error}";
    Self::Chain(error) => "chain map rejected: {error}";
    Self::ChainDomain => "chain map does not use the supplied source and target complexes";
    Self::HomotopyDomain => "homotopy does not use the supplied source and target complexes";
    Self::Defect { reason } => "internal transport check failed: {reason}";
} }

error_source! { TransportError {
    Self::Split(error) => Some(error),
    Self::Module(error) => Some(error),
    Self::Hom(error) => Some(error),
    Self::HomSpace(error) => Some(error),
    Self::Complex(error) => Some(error),
    Self::Chain(error) => Some(error),
    _ => None,
} }

from_variants! { TransportError {
    SplitError => Split,
    ModuleError => Module,
    HomError => Hom,
    HomSpaceError => HomSpace,
    BoundedComplexError => Complex,
    ChainMapError => Chain,
} }

/// A bounded complex whose terms carry verified membership in `add(T)`.
#[derive(Clone, Debug)]
pub struct AddTComplex {
    complex: BoundedComplex,
    witnesses: Vec<AddClosureWitness>,
}

impl AddTComplex {
    /// Builds a bounded `add(T)` complex from one witness per term.
    pub fn new(
        complex: BoundedComplex,
        witnesses: Vec<AddClosureWitness>,
    ) -> Result<AddTComplex, TransportError> {
        if witnesses.len() != complex.len() {
            return Err(TransportError::SourceWitnessCount {
                expected: complex.len(),
                got: witnesses.len(),
            });
        }
        for (term, (module, witness)) in complex.terms().iter().zip(&witnesses).enumerate() {
            if !witness.verify() {
                return Err(TransportError::InvalidSourceWitness { term });
            }
            if !witness.module().ptr_eq(module) {
                return Err(TransportError::SourceWitnessTerm { term });
            }
        }
        Ok(AddTComplex { complex, witnesses })
    }

    accessor_methods! {
        /// The bounded source complex.
        pub complex() -> &BoundedComplex = |this| &this.complex;
        /// One verified `add(T)` witness per source term.
        pub witnesses() -> &[AddClosureWitness] = |this| &this.witnesses;
    }

    /// Rechecks the complex and every stored term witness.
    pub fn verify(&self) -> bool {
        self.complex.verify()
            && self.witnesses.len() == self.complex.len()
            && self
                .complex
                .terms()
                .iter()
                .zip(&self.witnesses)
                .all(|(term, witness)| witness.verify() && witness.module().ptr_eq(term))
    }
}

#[derive(Clone, Debug)]
pub(super) struct SourceTerm {
    pub(super) module: Module,
    pub(super) split: Split,
    pub(super) indices: Vec<usize>,
    pub(super) to_target: Vec<Morphism>,
    pub(super) from_target: Vec<Morphism>,
}

impl SourceTerm {
    fn verify(&self, target_summands: &[Module]) -> bool {
        self.split.verify()
            && self.split.total().ptr_eq(&self.module)
            && self.indices.len() == self.split.summands().len()
            && self.to_target.len() == self.indices.len()
            && self.from_target.len() == self.indices.len()
            && self.indices.iter().enumerate().all(|(slot, &index)| {
                target_summands.get(index).is_some_and(|target| {
                    self.to_target[slot]
                        .source()
                        .ptr_eq(&self.split.summands()[slot])
                        && self.to_target[slot].target().ptr_eq(target)
                        && self.from_target[slot].source().ptr_eq(target)
                        && self.from_target[slot]
                            .target()
                            .ptr_eq(&self.split.summands()[slot])
                        && mutually_inverse(&self.to_target[slot], &self.from_target[slot])
                })
            })
    }
}

#[derive(Clone, Debug)]
pub(super) struct ProjectiveTerm {
    pub(super) module: Module,
    pub(super) split: Split,
    pub(super) indices: Vec<usize>,
    pub(super) to_canonical: Vec<Morphism>,
    pub(super) from_canonical: Vec<Morphism>,
    pub(super) source: SourceTerm,
}

impl ProjectiveTerm {
    fn verify(&self, target_summands: &[Module], canonical_projectives: &[Module]) -> bool {
        self.split.verify()
            && self.split.total().ptr_eq(&self.module)
            && self.indices.len() == self.split.summands().len()
            && self.to_canonical.len() == self.indices.len()
            && self.from_canonical.len() == self.indices.len()
            && self.source.verify(target_summands)
            && self.source.indices == self.indices
            && self.indices.iter().enumerate().all(|(slot, &index)| {
                canonical_projectives.get(index).is_some_and(|projective| {
                    self.to_canonical[slot]
                        .source()
                        .ptr_eq(&self.split.summands()[slot])
                        && self.to_canonical[slot].target().ptr_eq(projective)
                        && self.from_canonical[slot].source().ptr_eq(projective)
                        && self.from_canonical[slot]
                            .target()
                            .ptr_eq(&self.split.summands()[slot])
                        && mutually_inverse(&self.to_canonical[slot], &self.from_canonical[slot])
                })
            })
    }
}

/// A bounded target complex with a canonical-projective decomposition per term.
#[derive(Clone, Debug)]
pub struct ProjectiveTargetComplex {
    pub(super) complex: BoundedComplex,
    pub(super) terms: Vec<ProjectiveTerm>,
    pub(super) target_summands: Vec<Module>,
    pub(super) canonical_projectives: Vec<Module>,
}

impl ProjectiveTargetComplex {
    accessor_methods! {
        /// The bounded complex over the recovered target algebra.
        pub complex() -> &BoundedComplex = |this| &this.complex;
    }

    /// Rechecks every stored target term decomposition and the bounded complex.
    pub fn verify(&self) -> bool {
        self.complex.verify()
            && self.terms.len() == self.complex.len()
            && self
                .complex
                .terms()
                .iter()
                .zip(&self.terms)
                .all(|(term, model)| {
                    term.ptr_eq(&model.module)
                        && model.verify(&self.target_summands, &self.canonical_projectives)
                })
    }
}

/// Two mutually inverse checked chain maps.
#[derive(Clone, Debug)]
pub struct ChainIsomorphism {
    forward: ChainMap,
    backward: ChainMap,
}

impl ChainIsomorphism {
    /// Builds a chain isomorphism after checking both inverse identities.
    pub fn new(forward: ChainMap, backward: ChainMap) -> Result<ChainIsomorphism, TransportError> {
        let round = forward.then(&backward)?;
        let back = backward.then(&forward)?;
        if !round.agrees_with(&ChainMap::identity(forward.source()))
            || !back.agrees_with(&ChainMap::identity(forward.target()))
        {
            return Err(TransportError::Defect {
                reason: "stored chain maps are not mutual inverses".to_string(),
            });
        }
        Ok(ChainIsomorphism { forward, backward })
    }

    accessor_methods! {
        /// The forward chain map.
        pub forward() -> &ChainMap = |this| &this.forward;
        /// The inverse chain map.
        pub backward() -> &ChainMap = |this| &this.backward;
    }

    /// Rechecks both chain maps and both inverse identities.
    pub fn verify(&self) -> bool {
        self.forward.verify()
            && self.backward.verify()
            && ChainIsomorphism::new(self.forward.clone(), self.backward.clone()).is_ok()
    }
}

/// The strict additive transport fixed by one verified target presentation.
#[derive(Clone)]
pub struct StrictTransport {
    pub(super) target: VerifiedTargetPresentation,
    pub(super) source_basic: BasicDecomposition,
    pub(super) target_basic: BasicDecomposition,
    pub(super) canonical_projectives: Vec<Module>,
}

debug_fields!(StrictTransport |this| {
    "source_dim_vector" => this.target.source().dim_vector();
    "target_dim" => this.target.target().dim();
});

fn compose_three(
    first: &Morphism,
    second: &Morphism,
    third: &Morphism,
) -> Result<Morphism, TransportError> {
    Ok(first.then(second)?.then(third)?)
}

fn coordinate_matrix(
    source: &HomSpace,
    target: &HomSpace,
    mut image: impl FnMut(usize) -> Result<Morphism, TransportError>,
) -> Result<DenseMat, TransportError> {
    let mut matrix = DenseMat::zero(source.dim(), target.dim());
    for row in 0..source.dim() {
        for (column, value) in target.coords(&image(row)?)?.into_iter().enumerate() {
            matrix.set(row, column, value);
        }
    }
    Ok(matrix)
}

fn sum_terms(
    source: &Module,
    target: &Module,
    terms: impl IntoIterator<Item = Morphism>,
) -> Result<Morphism, TransportError> {
    let mut sum = zero_morphism(source, target)?;
    for term in terms {
        sum = add_morphisms(&sum, &term);
    }
    Ok(sum)
}

fn rebase_morphism(
    map: &Morphism,
    source: &Module,
    target: &Module,
) -> Result<Morphism, TransportError> {
    if !same_representation(map.source(), source) || !same_representation(map.target(), target) {
        return Err(TransportError::Defect {
            reason: "morphism endpoints do not match their checked representations".to_string(),
        });
    }
    let matrices = (0..source.algebra().quiver().num_vertices())
        .map(|vertex| map.map_at(vertex).clone())
        .collect();
    Morphism::new(source, target, matrices).map_err(Into::into)
}

fn agrees_after_padding(left: &BoundedComplex, right: &BoundedComplex) -> bool {
    let Ok(range) = DegreeRange::new(
        left.lower().min(right.lower()),
        left.upper().max(right.upper()),
    ) else {
        return false;
    };
    left.padded_to(range).is_ok_and(|left| {
        right
            .padded_to(range)
            .is_ok_and(|right| left.agrees_with(&right))
    })
}

fn transported_components(
    range: DegreeRange,
    source: (&BoundedComplex, &BoundedComplex),
    target: (&BoundedComplex, &BoundedComplex),
    family: (&[Morphism], usize),
    mut transport: impl FnMut(usize, usize, &Morphism) -> Result<Morphism, TransportError>,
) -> Result<Vec<Morphism>, TransportError> {
    let (components, target_offset) = family;
    let source_padded = source.1.padded_to(range)?;
    let target_padded = target.1.padded_to(range)?;
    (0..range.len().saturating_sub(target_offset))
        .map(|index| {
            let degree = (i64::from(range.lower()) + index as i64) as i32;
            let target_degree = degree
                .checked_add(target_offset as i32)
                .expect("the component range excludes target degree overflow");
            if source.0.range().contains(degree) && target.0.range().contains(target_degree) {
                transport(
                    (i64::from(degree) - i64::from(source.0.lower())) as usize,
                    (i64::from(target_degree) - i64::from(target.0.lower())) as usize,
                    &components[index],
                )
            } else {
                zero_morphism(
                    &source_padded.terms()[index],
                    &target_padded.terms()[index + target_offset],
                )
                .map_err(Into::into)
            }
        })
        .collect()
}

type ForwardSummandLists = (Vec<Module>, Vec<Morphism>, Vec<Morphism>);

#[derive(Clone, Debug)]
struct ForwardTerm {
    module: Module,
    homs: Vec<HomSpace>,
    projective: ProjectiveTerm,
    unit: Morphism,
    unit_inverse: Morphism,
}

#[path = "transport/build.rs"]
mod build;
#[path = "transport/ops.rs"]
mod ops;
