//! Python bindings for the `auslander` crate: prime fields, quivers, bound
//! quiver algebras with monomial or general admissible relations, and their
//! right modules.
//!
//! The surface is algebra-owned. Modules are created only through `Algebra`
//! methods, so every Python-visible `Module` is a validated `kQ/I`-module.
//! Library errors cross the boundary as `ValueError` carrying the Rust
//! `Display` message. A rejection with variants gets one `ValueError` subclass
//! per variant, with its payload attached as attributes, so the failed
//! precondition is never reduced to a message string. Engine limits and
//! defects are `RuntimeError`, never `ValueError`.
//!
//! A mathematical outcome never raises. A pair that fails a condition is a
//! `PairRejection` value, a slot with no left mutation is a `FacWitness`, and a
//! mutation walk that stops short is an
//! `IncompleteSupportTauTiltingGraph` carrying its reason. The two graph
//! outcomes are two classes, and only the closed one has a `pairs` accessor, so
//! a completeness claim cannot be read off a truncated walk.

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Mutex};

use pyo3::IntoPyObjectExt;
use pyo3::exceptions::{PyBaseException, PyOverflowError, PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::sync::GILOnceCell;

use auslander::algebra::{self, Algebra, AlgebraBuildError};
use auslander::almost_split::{self, AlmostSplitError, AlmostSplitOutcome, AlmostSplitWitness};
use auslander::approx::ApproxError;
use auslander::ar;
use auslander::arquiver::{
    self, ArQuiver, ArQuiverError, ArrowValuation, CatalogProvenance, IndecomposableCatalog,
};
use auslander::basic::{AddClosureWitness, BasicDecomposition, BasicError, ProjectiveSupport};
use auslander::batch::{
    HomologicalBatch, HomologicalBatchError, HomologicalBatchLimits, HomologicalBatchWork,
    HomologicalPair,
};
use auslander::batch_stream::{
    HomologicalBatchStreamLimits, HomologicalBatchStreamRow, HomologicalBatchStreamWork,
    HomologicalSelfPairCheckpointStream, HomologicalStreamBudget, HomologicalStreamConfig,
    HomologicalStreamCutReason, HomologicalStreamParseLimits, HomologicalStreamPortable,
    HomologicalStreamPortableError, HomologicalStreamPortableStatus, HomologicalStreamStep,
    HomologicalStreamVerifyLimits, VerifiedHomologicalStream, homological_stream_from_census,
};
use auslander::census::{
    Census, CensusCutReason, CensusLimits, CensusOutcome, CensusParseLimits, CensusPortable,
    CensusPortableAssignment, CensusPortableError, CensusPortableRepresentative,
    CensusPortableStatus, CensusResumeError, CensusRetention, CensusVerifyLimits, CensusWorkStage,
    VerifiedCensus,
};
use auslander::completion::{CompletionLimits, TruncationDiagnostics, TruncationReason};
use auslander::complex::{
    CheckedComplex, ExactComplex, ExactnessOutcome, HomologyDimensions, NonExactWitness,
};
use auslander::control::{ComputationControl, ProgressStage};
use auslander::decompose::{self, Certificate, KrullSchmidtOutcome};
use auslander::derived::{
    AddTComplex as RustAddTComplex, ChainIsomorphism as RustChainIsomorphism,
    DegreeZeroEndIdentification, DerivedCertificateError as RustDerivedCertificateError,
    DerivedEquivalenceCertificate as RustDerivedEquivalenceCertificate,
    GradedHomotopyEndomorphisms, ProjectiveTargetComplex as RustProjectiveTargetComplex,
    StrictTransport as RustStrictTransport, TransportError,
};
use auslander::derived_artifact::{
    ArtifactError, ArtifactVerificationCut, ArtifactVerificationOutcome, ArtifactVerifyLimits,
    DerivedArtifact as RustDerivedArtifact, VerifiedDerivedArtifact,
    verify_derived_artifact as verify_artifact,
};
use auslander::derived_hom::{
    DerivedHom as RustDerivedHom, DerivedHomCancellation, DerivedHomCut, DerivedHomLimits,
    DerivedHomOutcome, derived_hom,
};
use auslander::derived_transport::{
    DerivedForwardOutcome, DerivedForwardTransport, DerivedReverseOutcome, DerivedReverseTransport,
    DerivedTransport as RustDerivedTransport,
};
use auslander::dynkin::{self, DynkinType, EuclideanType};
use auslander::enumerate;
use auslander::equivalence_discovery::{
    BlockedMutationReason, DiscoveryLimits, DiscoveryStop, IncompleteEquivalenceGraph,
    discover_equivalences as discover_tilting_equivalences,
};
use auslander::equivalence_edge::{
    DerivedEquivalenceEdge as RustDerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome,
};
use auslander::ext::{self, ExtClassError, ExtError, ProductWitness};
use auslander::extalgebra::{
    ExtAlgebra as RustExtAlgebra, ExtAlgebraCut, ExtAlgebraError, ExtAlgebraOutcome,
    ExtAlgebraProductError, MultiplicationTensor,
};
use auslander::field::{Fp, PrimeField};
use auslander::hochschild::{
    BarBudgetDiagnostics, BarCutReason, BarInput, BarLimit, BarLimits, BarRunDiagnostics, BarStage,
    HochschildClass, HochschildCohomology, HochschildDegree, HochschildError, HochschildOutcome,
    IncompleteHochschildCohomology, bar_hochschild,
};
use auslander::hom;
use auslander::homotopy::{
    BoundedComplex, BoundedComplexError, ChainHomQuotient, ChainHomotopy, ChainMap, ChainMapError,
    HomotopyHom, HomotopyHomQuotient,
};
use auslander::homspace::{HomQuotient, HomSubspace};
use auslander::indec::{IndecError, IndecomposableModule};
use auslander::injective::{self, Cosyzygy, CosyzygyWitness, InjectiveCoresolution, cosyzygy};
use auslander::iso::{self, IsoOutcome, Obstruction};
use auslander::linalg::DenseMat;
use auslander::module::{Module, direct_sum};
use auslander::monomial::{self, MonomialIdeal, MonomialPresentation};
use auslander::mutation::{
    ExchangeShape, FacWitness, Mutation, MutationError, SlotOutcome, mutate_at,
};
use auslander::perfect::{
    PerfectReplacement as RustPerfectReplacement, ReplacementCancellation, ReplacementCut,
    ReplacementLimits, ReplacementOutcome, replace_perfect,
};
use auslander::quiver::{ArrowId, Quiver};
use auslander::radical;
use auslander::relation::{Presentation, Relation};
use auslander::resolution::{
    Bounded, ProjectiveResolution, ResolutionEnd, Syzygy, SyzygyWitness, projective_cover,
    projective_dimension, resolve, syzygy,
};
use auslander::sequence::{self, SequenceError, SplitStatus};
use auslander::supporttau::{
    self, AlmostCompleteClassification, AlmostCompletePair, CatalogEnumeration, PairRejection,
    SupportTauError, SupportTauTiltingClassification, SupportTauTiltingPair,
};
use auslander::target::{
    NonSplitTarget, TargetCutReason, TargetCutStage, TargetLimits, TargetPresentationCut,
    TargetPresentationOutcome, TargetWork, VerifiedTargetPresentation, present_target,
};
use auslander::taugraph::{
    self, CertificationBlocker, ClosedSupportTauTiltingGraph, GraphBudgetDiagnostics, GraphError,
    IncompleteReason, IncompleteSupportTauTiltingGraph, MutationGraphLimits,
    SupportTauTiltingGraphOutcome, VerifiedMutation,
};
use auslander::taurigid::{
    self, NonTauRigidWitness, TauRigidError, TauRigidModule, TauRigidityOutcome,
};
use auslander::tilting::{
    self, ClassicalTiltingResult as RustClassicalTiltingResult, GenerationBlocker, TiltingBlocker,
    TiltingError, TiltingLimits,
};
use auslander::tilting_complex::{
    ApproximationDirection, CertifiedTiltingComplex, TiltingComplexLimits, TiltingComplexResult,
    TiltingMutationOutcome, left_tilting_mutation, regular_tilting_complex, right_tilting_mutation,
};
use auslander::verify;

mod algebra_bindings;
mod ar_bindings;
mod artifact_bindings;
mod atlas_bindings;
mod batch_bindings;
mod catalog_bindings;
mod census_bindings;
mod complex_bindings;
mod complex_maps_bindings;
mod coordinate_bindings;
mod decomposition_bindings;
mod derived_complex_bindings;
mod derived_hom_bindings;
mod derived_transport_bindings;
mod dynkin_bindings;
mod equivalence_bindings;
mod error_bindings;
mod ext_algebra_bindings;
mod ext_classes_bindings;
mod field_quiver_bindings;
mod graph_bindings;
mod hochschild_bindings;
mod homological_checkpoint_bindings;
mod homotopy_bindings;
mod module_bindings;
mod morphism_bindings;
mod mutation_bindings;
mod resolution_bindings;
mod sequence_bindings;
mod support;
mod target_bindings;
mod tau_support_bindings;
mod theorem_artifact_bindings;
mod tilting_bindings;

pub(crate) use algebra_bindings::*;
pub(crate) use ar_bindings::*;
pub(crate) use artifact_bindings::*;
pub(crate) use atlas_bindings::*;
pub(crate) use batch_bindings::*;
pub(crate) use catalog_bindings::*;
pub(crate) use census_bindings::*;
pub(crate) use complex_bindings::*;
pub(crate) use complex_maps_bindings::*;
pub(crate) use coordinate_bindings::*;
pub(crate) use decomposition_bindings::*;
pub(crate) use derived_complex_bindings::*;
pub(crate) use derived_hom_bindings::*;
pub(crate) use derived_transport_bindings::*;
pub(crate) use dynkin_bindings::*;
pub(crate) use equivalence_bindings::*;
pub(crate) use error_bindings::*;
pub(crate) use ext_algebra_bindings::*;
pub(crate) use ext_classes_bindings::*;
pub(crate) use field_quiver_bindings::*;
pub(crate) use graph_bindings::*;
pub(crate) use hochschild_bindings::*;
pub(crate) use homological_checkpoint_bindings::*;
pub(crate) use homotopy_bindings::*;
pub(crate) use module_bindings::*;
pub(crate) use morphism_bindings::*;
pub(crate) use mutation_bindings::*;
pub(crate) use resolution_bindings::*;
pub(crate) use sequence_bindings::*;
pub(crate) use support::*;
pub(crate) use target_bindings::*;
pub(crate) use tau_support_bindings::*;
pub(crate) use theorem_artifact_bindings::*;
pub(crate) use tilting_bindings::*;

macro_rules! add_classes {
    ($module:expr; $($class:ty),+ $(,)?) => {
        $($module.add_class::<$class>()?;)+
    };
}

macro_rules! add_exceptions {
    ($module:expr; $($exception:ty),+ $(,)?) => {
        $($module.add(stringify!($exception), $module.py().get_type::<$exception>())?;)+
    };
}

macro_rules! add_functions {
    ($module:expr; $($function:ident),+ $(,)?) => {
        $($module.add_function(wrap_pyfunction!($function, $module)?)?;)+
    };
}

/// Finite-dimensional basic algebras kQ/I over a checked prime field, where I
/// is an admissible ideal given by forbidden words or by general relations,
/// and their finite-dimensional right modules. Convention: paths compose left
/// to right, and modules are right modules whose arrow matrices act on row
/// vectors.
#[pymodule(name = "_core")]
fn auslander_py(m: &Bound<'_, PyModule>) -> PyResult<()> {
    add_classes!(m;
        PyPrimeField,
        PyQuiver,
        PyAlgebra,
        PyIndecomposableCatalog,
        PyHigherOrthogonalityLimits,
        PyHigherExtPair,
        PyHigherOrthogonalityWork,
        PyHigherOrthogonality,
        PyCatalogAtlas,
        PyCatalogAtlasLimits,
        PyCatalogAtlasWork,
        PyCatalogExtRow,
        PyCatalogExtTable,
        PyMultiplicityLimits,
        PyMultiplicityCutReason,
        PyMultiplicityComplete,
        PyMultiplicityCut,
        PyMultiplicityResult,
        PyCatalogAtlasArtifactParseLimits,
        PyCatalogAtlasArtifactVerifyLimits,
        PyCatalogAtlasArtifactExtRow,
        PyCatalogAtlasArtifactResultRow,
        PyCatalogAtlasArtifactStatus,
        PyCatalogAtlasArtifact,
        PyVerifiedCatalogAtlasArtifact,
        PyCatalogCoordinateLimits,
        PyCatalogCoordinateMatch,
        PyCatalogCoordinateProgress,
        PyCatalogCoordinates,
        PyCatalogCoordinateUnknownReason,
        PyCatalogCoordinateUnknown,
        PyCatalogCoordinateCutReason,
        PyCatalogCoordinateCut,
        PyRightModule,
        PyMorphism,
        PyStableHomSpace,
        PyHomologicalBatchLimits,
        PyHomologicalPair,
        PyHomologicalBatchWork,
        PyHomologicalBatch,
        PyHomologicalStreamBudget,
        PyHomologicalStreamConfig,
        PyHomologicalStreamVerifyLimits,
        PyHomologicalStreamCutReason,
        PyHomologicalStreamRow,
        PyHomologicalStreamWork,
        PyHomologicalCheckpoint,
        PyVerifiedHomologicalCheckpoint,
        PyHomologicalCheckpointStream,
        PySelfExtLocusVerifyLimits,
        PySelfExtLocusArtifact,
        PyVerifiedSelfExtLocusArtifact,
        PyCensusLimits,
        PyCensusVerifyLimits,
        PyCensusRepresentative,
        PyCensusAssignment,
        PyCensusCutReason,
        PyCensusCheckpoint,
        PyVerifiedCensusCheckpoint,
        PyIsoResult,
        PyCertificate,
        PyDecomposition,
        PyKrullSchmidtResult,
        PyCheckedComplex,
        PyHomologyDimensions,
        PyNonExactWitness,
        PyExactComplex,
        PyComputationControl,
        PyReplacementLimits,
        PyPerfectReplacement,
        PyIncompletePerfectReplacement,
        PyDerivedHomLimits,
        PyDerivedHom,
        PyIncompleteDerivedHom,
        PyBoundedComplex,
        PyChainMap,
        PyChainHomotopy,
        PyHomotopyHom,
        PyHomotopyHomQuotient,
        PyChainHomQuotient,
        PyResolutionKind,
        PyResolutionStatus,
        PyResolution,
        PyInjectiveCoresolution,
        PySyzygy,
        PyCosyzygy,
        PyBounded,
        PyDiagramFamily,
        PyDynkinType,
        PyEuclideanType,
        PyExtSpace,
        PyExtClass,
        PyExtProductWitness,
        PyExtAlgebra,
        PyIncompleteExtAlgebra,
        PyExtMultiplication,
        PyExtProductRecord,
        PySplitWitness,
        PyNonSplitWitness,
        PyShortExactSequence,
        PyAlmostSplitOutcome,
        PyAlmostSplitSequence,
        PyCategoryRadical,
        PyArVertex,
        PyArArrow,
        PyArQuiver,
        PyTauRigidModule,
        PyTauRigidity,
        PyPairRejection,
        PySupportTauTiltingPair,
        PyAlmostCompletePair,
        PyFacWitness,
        PyMutation,
        PyMutationGraphLimits,
        PyGraphBudgetDiagnostics,
        PyCertificationBlocker,
        PyClosedSupportTauTiltingGraph,
        PyIncompleteSupportTauTiltingGraph,
        PyCatalogEnumeration,
        PyAddClosureWitness,
        PyBarLimits,
        PyBarBudgetDiagnostics,
        PyBarRunDiagnostics,
        PyHochschildCohomology,
        PyIncompleteHochschildCohomology,
        PyHochschildDegree,
        PyHochschildClass,
        PyTiltingLimits,
        PyTargetLimits,
        PyTargetWork,
        PyTargetPresentation,
        PyUnsupportedTarget,
        PyIncompleteTargetPresentation,
        PyClassicalTiltingResult,
        PyClassicalTiltingModule,
        PyPositiveSelfExtension,
        PyTiltingBlocker,
        PyAddTComplex,
        PyProjectiveTargetComplex,
        PyChainIsomorphism,
        PyStrictTransport,
        PyGradedHomotopyEndomorphisms,
        PyDegreeZeroEndIdentification,
        PyDerivedEquivalenceCertificate,
        PyDerivedTransport,
        PyDerivedTransportResult,
        PyEquivalenceDiscoveryLimits,
        PyIncompleteEquivalenceGraph,
        PyVerifiedDerivedArtifact,
        PyIncompleteArtifactVerification,
    );
    add_exceptions!(m;
        TauAgreementUnknown,
        BudgetExhaustedError,
        TruncationError,
        DefectError,
        TransportInputError,
        DerivedCertificateError,
        CertificationBlockedError,
        NotIndecomposableError,
        IncompatibleSpacesError,
        UnsupportedDomainError,
        ValuedArrowError,
        DynkinError,
        NonzeroIdealError,
        NotDynkinError,
    );
    add_functions!(m;
        catalog,
        higher_orthogonality,
        verify_catalog_atlas_artifact,
        global_dimension,
        nakayama_indecomposables,
        dynkin_type,
        euclidean_type,
        generalized_cartan_matrix,
        positive_roots,
        dynkin_quiver,
        euclidean_quiver,
        dynkin_indecomposables,
        discover_equivalences,
        run_census,
        verify_census_checkpoint,
        start_homological_stream,
        verify_homological_checkpoint,
        build_self_ext_locus_artifact,
        verify_self_ext_locus_artifact,
        build_derived_artifact,
        py_verify_derived_artifact,
    );
    Ok(())
}
