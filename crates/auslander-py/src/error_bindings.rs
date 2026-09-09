use super::*;
use pyo3::create_exception;

pub(crate) fn value_error(e: impl std::fmt::Display) -> PyErr {
    PyValueError::new_err(e.to_string())
}

pub(crate) fn bounded_complex_error(e: BoundedComplexError) -> PyErr {
    match e {
        BoundedComplexError::DegreeOverflow { .. } => PyOverflowError::new_err(e.to_string()),
        other => value_error(other),
    }
}

pub(crate) fn homotopy_error(e: ChainMapError) -> PyErr {
    match e {
        ChainMapError::DegreeOverflow { .. }
        | ChainMapError::Padding(BoundedComplexError::DegreeOverflow { .. }) => {
            PyOverflowError::new_err(e.to_string())
        }
        other => value_error(other),
    }
}

/// An engine limit or defect (a failed pipeline run inside the library), not
/// bad input. It becomes a RuntimeError, like the tau cross-check failures.
pub(crate) fn engine_error(e: impl std::fmt::Display) -> PyErr {
    PyRuntimeError::new_err(e.to_string())
}

pub(crate) fn completion_reason_name(reason: TruncationReason) -> &'static str {
    match reason {
        TruncationReason::BasisBudget => "basis_budget",
        TruncationReason::WordLenBudget => "word_len_budget",
        TruncationReason::StepBudget => "step_budget",
        TruncationReason::OriginBudget => "origin_budget",
        TruncationReason::AmbiguityBudget => "ambiguity_budget",
    }
}

/// The error with its payload attached to the exception value, or the failure
/// the attaching itself raised. Takes the GIL, so it must run outside any
/// `allow_threads` region.
pub(crate) fn attach(
    err: PyErr,
    f: impl FnOnce(&Bound<'_, PyBaseException>) -> PyResult<()>,
) -> PyErr {
    Python::with_gil(|py| match f(err.value(py)) {
        Ok(()) => err,
        Err(failure) => failure,
    })
}

/// An exhausted completion budget as a TruncationError with the diagnostics
/// counts attached as attributes, so the consumed budget survives the boundary.
pub(crate) fn truncation_error(d: &TruncationDiagnostics) -> PyErr {
    let reason = completion_reason_name(d.reason);
    let err = TruncationError::new_err(format!(
        "completion ran out of budget ({reason}): basis {}, pending ambiguities {}, steps {}",
        d.basis_len, d.pending_ambiguities, d.steps_used
    ));
    attach(err, |value| {
        value.setattr("basis_len", d.basis_len)?;
        value.setattr("pending_ambiguities", d.pending_ambiguities)?;
        value.setattr("steps_used", d.steps_used)?;
        value.setattr("reason", reason)
    })
}

/// A build failure of an initial construction, where the presentation is
/// user input. Rejected input is ValueError with the Rust message; an
/// infinite-dimensional quotient is rejected input too, and its message
/// carries the witness words. An exhausted budget is TruncationError (a
/// RuntimeError). A certificate the verifier rejected for any other reason
/// is an engine defect: plain RuntimeError.
pub(crate) fn build_error(e: AlgebraBuildError) -> PyErr {
    match e {
        AlgebraBuildError::Monomial(_)
        | AlgebraBuildError::Relation(_)
        | AlgebraBuildError::InfiniteDimensional { .. }
        | AlgebraBuildError::NonAdmissible { .. }
        | AlgebraBuildError::InputRelationsMismatch { .. } => value_error(e),
        AlgebraBuildError::Truncated(d) => truncation_error(&d),
        AlgebraBuildError::Verification(_) => engine_error(e),
    }
}

/// A build failure of a derived completion (the opposite algebra under
/// tau, injective envelopes, coresolutions, and injective dimensions).
/// An exhausted budget is TruncationError with the diagnostics attached.
/// Everything else is RuntimeError: the reversed relations come from a
/// verified algebra, so an infinite opposite or a rejected reversed
/// relation is a library defect, not user input.
pub(crate) fn downstream_build_error(e: AlgebraBuildError) -> PyErr {
    match e {
        AlgebraBuildError::Truncated(d) => truncation_error(&d),
        other => engine_error(other),
    }
}

/// A failed AR translate, mapped as `Module.tau` documents: an exhausted
/// budget is TruncationError, a certified disagreement is DefectError (the two
/// routes are a cross-check of one theorem), and an undecided cross-check is
/// TauAgreementUnknown. All three subclass RuntimeError.
pub(crate) fn tau_error(e: ar::TauError) -> PyErr {
    match e {
        ar::TauError::Opposite(build) => downstream_build_error(build),
        e @ ar::TauError::RoutesDisagree { .. } => DefectError::new_err(e.to_string()),
        e @ ar::TauError::AgreementUnknown { .. } => TauAgreementUnknown::new_err(e.to_string()),
    }
}

/// A module the indecomposability gate refused, as NotIndecomposableError with
/// the gate's report attached: `kind` is "zero", "decomposable" or
/// "undetermined", `summands` counts the certified summands of a decomposable
/// module, and `attempts` counts the exhausted split attempts of an
/// undetermined one. `what` names the rejected endpoint.
pub(crate) fn indec_error(what: &str, e: IndecError) -> PyErr {
    let kind = match e {
        IndecError::Zero => "zero",
        IndecError::Decomposable { .. } => "decomposable",
        IndecError::Undetermined { .. } => "undetermined",
    };
    let summands = match e {
        IndecError::Decomposable { summands } => Some(summands),
        _ => None,
    };
    let attempts = match e {
        IndecError::Undetermined { attempts } => Some(attempts),
        _ => None,
    };
    let err =
        NotIndecomposableError::new_err(format!("{what} is not certified indecomposable: {e}"));
    attach(err, |value| {
        value.setattr("kind", kind)?;
        value.setattr("summands", summands)?;
        value.setattr("attempts", attempts)
    })
}

/// A rejected Ext class operation. Operands that do not share one space are
/// IncompatibleSpacesError, so a comparison never quietly answers False;
/// everything else is rejected input, so ValueError.
pub(crate) fn ext_class_error(e: ExtClassError) -> PyErr {
    match e {
        ExtClassError::IncompatibleSpaces | ExtClassError::MiddleMismatch => {
            IncompatibleSpacesError::new_err(e.to_string())
        }
        ExtClassError::DegreeOverflow { .. } => PyOverflowError::new_err(e.to_string()),
        other => value_error(other),
    }
}

pub(crate) fn ext_error(e: ExtError) -> PyErr {
    match e {
        ExtError::DegreeOverflow { .. } => PyOverflowError::new_err(e.to_string()),
        other => value_error(other),
    }
}

pub(crate) fn ext_algebra_error(e: ExtAlgebraError) -> PyErr {
    match e {
        ExtAlgebraError::DegreeOverflow => PyOverflowError::new_err(e.to_string()),
        other => DefectError::new_err(other.to_string()),
    }
}

pub(crate) fn ext_algebra_product_error(e: ExtAlgebraProductError) -> PyErr {
    match e {
        ExtAlgebraProductError::OutsideAlgebra
        | ExtAlgebraProductError::IncompatibleBasis { .. } => {
            IncompatibleSpacesError::new_err(e.to_string())
        }
        ExtAlgebraProductError::DegreeOutsideBound { .. }
        | ExtAlgebraProductError::DegreeSumOutsideBound { .. } => value_error(e),
    }
}

pub(crate) fn target_error(e: auslander::target::TargetError) -> PyErr {
    match e {
        auslander::target::TargetError::Basic(error) => basic_error(error),
        auslander::target::TargetError::SizeOverflow { .. } => {
            PyOverflowError::new_err(e.to_string())
        }
        auslander::target::TargetError::Relation(_)
        | auslander::target::TargetError::Algebra(_)
        | auslander::target::TargetError::Defect { .. } => DefectError::new_err(e.to_string()),
    }
}

/// A rejected short exact sequence operation. A wrong degree is caller input,
/// so ValueError; every other variant reports a structural check on a sequence
/// this package built itself, so RuntimeError.
pub(crate) fn sequence_error(e: SequenceError) -> PyErr {
    match e {
        SequenceError::WrongDegree { .. } => value_error(e),
        other => engine_error(other),
    }
}

/// A failed AR-quiver or category-radical call. An algebra outside the two
/// catalog domains is UnsupportedDomainError naming both failed routes;
/// everything else is DefectError. Both entry points validate their endpoints
/// before the call, so a mismatched hom endpoint or space here means the crate
/// contradicted itself, exactly like a failed internal division or containment.
pub(crate) fn ar_quiver_error(e: ArQuiverError) -> PyErr {
    match e {
        ArQuiverError::UnsupportedDomain { .. } => UnsupportedDomainError::new_err(e.to_string()),
        ArQuiverError::Injective(build) => downstream_build_error(build),
        e @ (ArQuiverError::Hom(_)
        | ArQuiverError::Space(_)
        | ArQuiverError::RadicalSquareNotContained { .. }
        | ArQuiverError::ResidueDegreeDoesNotDivide { .. }) => DefectError::new_err(e.to_string()),
    }
}

/// A failed almost-split construction. A translate that fails the
/// indecomposability gate and a failed internal cross-check are both crate
/// defects, so DefectError; the remaining variants keep the mapping of the
/// layer they come from.
pub(crate) fn almost_split_error(e: AlmostSplitError) -> PyErr {
    match e {
        AlmostSplitError::Tau(inner) => tau_error(inner),
        AlmostSplitError::Ext(inner) => ext_class_error(inner),
        AlmostSplitError::Sequence(inner) => sequence_error(inner),
        AlmostSplitError::Radical(inner) => ar_quiver_error(inner),
        e @ (AlmostSplitError::TauIndecomposability(_) | AlmostSplitError::Defect(_)) => {
            DefectError::new_err(e.to_string())
        }
        e @ (AlmostSplitError::Hom(_) | AlmostSplitError::Space(_)) => engine_error(e),
    }
}

/// A rejected batch shape, exhausted preflight limit, or failed primitive.
pub(crate) fn homological_batch_error(e: HomologicalBatchError) -> PyErr {
    match e {
        HomologicalBatchError::DegreeOverflow { .. } => PyOverflowError::new_err(e.to_string()),
        HomologicalBatchError::PairLimit { .. } | HomologicalBatchError::ExtCellLimit { .. } => {
            BudgetExhaustedError::new_err(e.to_string())
        }
        HomologicalBatchError::DifferentAlgebra { .. }
        | HomologicalBatchError::PairIndex { .. }
        | HomologicalBatchError::ResultIndex { .. }
        | HomologicalBatchError::DuplicatePair { .. } => PyValueError::new_err(e.to_string()),
        HomologicalBatchError::Hom { error, .. } => value_error(error),
        HomologicalBatchError::StableHom { error, .. } => almost_split_error(error),
    }
}

/// A failed basic-layer call. A summand the crate could not certify is
/// CertificationBlockedError, a failed cross-check is DefectError, and the
/// remaining variants are rejected input.
pub(crate) fn basic_error(e: BasicError) -> PyErr {
    match e {
        e @ BasicError::CertificationBlocked { .. } => {
            CertificationBlockedError::new_err(e.to_string())
        }
        e @ BasicError::Defect { .. } => DefectError::new_err(e.to_string()),
        other => value_error(other),
    }
}

/// A failed tau-rigidity call, mapped as the layer it comes from.
pub(crate) fn tau_rigid_error(e: TauRigidError) -> PyErr {
    match e {
        TauRigidError::Tau(inner) => tau_error(inner),
        TauRigidError::Hom(inner) => value_error(inner),
    }
}

/// A failed approximation call. An add-generator the gate left undetermined is
/// CertificationBlockedError, a failed cross-check is DefectError.
pub(crate) fn approx_error(e: ApproxError) -> PyErr {
    match e {
        e @ ApproxError::SummandNotIndecomposable {
            reason: IndecError::Undetermined { .. },
            ..
        } => CertificationBlockedError::new_err(e.to_string()),
        e @ ApproxError::Defect(_) => DefectError::new_err(e.to_string()),
        other => value_error(other),
    }
}

/// A failed support tau-tilting call. A pair that fails a condition never comes
/// through here: that is a PairRejection value on the classification.
pub(crate) fn support_tau_error(e: SupportTauError) -> PyErr {
    match e {
        SupportTauError::Basic(inner) => basic_error(inner),
        SupportTauError::TauRigid(inner) => tau_rigid_error(inner),
        SupportTauError::Hom(inner) => value_error(inner),
        e @ SupportTauError::Defect { .. } => DefectError::new_err(e.to_string()),
        other => value_error(other),
    }
}

/// A failed mutation call. A slot with no left mutation never comes through
/// here: that is a FacWitness value.
pub(crate) fn mutation_error(e: MutationError) -> PyErr {
    match e {
        MutationError::Basic(inner) => basic_error(inner),
        MutationError::SupportTau(inner) => support_tau_error(inner),
        MutationError::Approx(inner) => approx_error(inner),
        e @ MutationError::Indec(IndecError::Undetermined { .. }) => {
            CertificationBlockedError::new_err(e.to_string())
        }
        MutationError::Indec(inner) => indec_error("a cokernel summand", inner),
        e @ MutationError::Defect(_) => DefectError::new_err(e.to_string()),
        other => value_error(other),
    }
}

/// A failed mutation-graph call. A budget that ran out and a blocked
/// certification never come through here: both are IncompleteReason values on
/// IncompleteSupportTauTiltingGraph.
pub(crate) fn graph_error(e: GraphError) -> PyErr {
    match e {
        GraphError::Basic(inner) => basic_error(inner),
        GraphError::SupportTau(inner) => support_tau_error(inner),
        GraphError::Mutation(inner) => mutation_error(inner),
        e @ GraphError::Defect { .. } => DefectError::new_err(e.to_string()),
    }
}

/// A failed classical-tilting call. A rejected basic candidate keeps the
/// basic layer's mapping. Every later error contradicts an internal checked
/// construction and becomes DefectError.
pub(crate) fn tilting_error(e: TiltingError) -> PyErr {
    match e {
        TiltingError::Basic(inner) => basic_error(inner),
        e @ (TiltingError::Approx(_)
        | TiltingError::Ext(_)
        | TiltingError::Complex(_)
        | TiltingError::Defect { .. }) => DefectError::new_err(e.to_string()),
    }
}

/// A rejected strict transport call. Endpoint and witness mismatches are
/// caller input, while a failed checked construction is a DefectError.
pub(crate) fn transport_error(e: TransportError) -> PyErr {
    match e {
        TransportError::SourceWitnessCount { expected, got } => {
            attach(TransportInputError::new_err(e.to_string()), |value| {
                value.setattr("expected", expected)?;
                value.setattr("got", got)
            })
        }
        TransportError::InvalidSourceWitness { term }
        | TransportError::SourceWitnessTarget { term }
        | TransportError::SourceWitnessTerm { term }
        | TransportError::TargetTermNotProjective { term } => {
            attach(TransportInputError::new_err(e.to_string()), |value| {
                value.setattr("term", term)
            })
        }
        TransportError::TargetSummandMatch { term, summand }
        | TransportError::SourceSummandMatch { term, summand } => {
            attach(TransportInputError::new_err(e.to_string()), |value| {
                value.setattr("term", term)?;
                value.setattr("summand", summand)
            })
        }
        TransportError::ChainDomain | TransportError::HomotopyDomain => {
            TransportInputError::new_err(e.to_string())
        }
        e @ (TransportError::InvalidTarget
        | TransportError::Isomorphism { .. }
        | TransportError::Split(_)
        | TransportError::Module(_)
        | TransportError::Hom(_)
        | TransportError::HomSpace(_)
        | TransportError::Complex(_)
        | TransportError::Chain(_)
        | TransportError::Defect { .. }) => DefectError::new_err(e.to_string()),
    }
}

/// A failed consistency check while building a derived-equivalence certificate.
pub(crate) fn derived_certificate_error(e: RustDerivedCertificateError) -> PyErr {
    match e {
        RustDerivedCertificateError::ResolutionCut { at } => {
            attach(DerivedCertificateError::new_err(e.to_string()), |value| {
                value.setattr("at", at)
            })
        }
        RustDerivedCertificateError::ResolutionTermNotProjective { term } => {
            attach(DerivedCertificateError::new_err(e.to_string()), |value| {
                value.setattr("term", term)
            })
        }
        RustDerivedCertificateError::NonzeroSelfHom { degree, dimension } => {
            attach(DerivedCertificateError::new_err(e.to_string()), |value| {
                value.setattr("degree", degree)?;
                value.setattr("dimension", dimension)
            })
        }
        RustDerivedCertificateError::DegreeZeroDimension {
            homotopy,
            endomorphism,
        } => attach(DerivedCertificateError::new_err(e.to_string()), |value| {
            value.setattr("homotopy_dimension", homotopy)?;
            value.setattr("endomorphism_dimension", endomorphism)
        }),
        RustDerivedCertificateError::DegreeOverflow { width } => {
            attach(DerivedCertificateError::new_err(e.to_string()), |value| {
                value.setattr("width", width)
            })
        }
        RustDerivedCertificateError::Transport(inner) => transport_error(inner),
        other => DerivedCertificateError::new_err(other.to_string()),
    }
}

/// A rejected bar-class input is ValueError. A nonzero internally generated
/// differential square contradicts the construction and becomes DefectError.
pub(crate) fn hochschild_error(e: HochschildError) -> PyErr {
    match e {
        e @ HochschildError::DifferentialSquare { .. } => DefectError::new_err(e.to_string()),
        other => value_error(other),
    }
}

pub(crate) fn bar_limit_name(limit: BarLimit) -> &'static str {
    match limit {
        BarLimit::TensorTuples => "max_tensor_tuples",
        BarLimit::CochainDimension => "max_cochain_dim",
        BarLimit::MatrixEntries => "max_matrix_entries",
        BarLimit::WorkUnits => "max_work_units",
    }
}

pub(crate) fn bar_reason_name(reason: BarCutReason) -> &'static str {
    match reason {
        BarCutReason::Limit(limit) => bar_limit_name(limit),
        BarCutReason::SizeOverflow => "size_overflow",
    }
}

pub(crate) fn bar_stage_name(stage: BarStage) -> &'static str {
    match stage {
        BarStage::DegreeRecord => "degree_record",
        BarStage::Shape => "shape",
        BarStage::Layout => "layout",
        BarStage::Differential => "differential",
        BarStage::Square => "square",
        BarStage::Cocycles => "cocycles",
        BarStage::Coboundaries => "coboundaries",
        BarStage::Complement => "complement",
    }
}

create_exception!(
    auslander,
    TauAgreementUnknown,
    PyRuntimeError,
    "The two tau routes were computed but the isomorphism test could not certify \
     them equal or unequal. This is a limit of that test, not evidence that the \
     routes disagree; a certified disagreement raises RuntimeError itself."
);

create_exception!(
    auslander,
    BudgetExhaustedError,
    PyRuntimeError,
    "An enforced work budget ran out before the computation finished. Nothing \
     is claimed about the result; raise the limits and run again. The variant \
     is the subclass."
);

create_exception!(
    auslander,
    TruncationError,
    BudgetExhaustedError,
    "Completion ran out of budget before it produced a certificate. The \
     consumed budget is attached: `basis_len`, `pending_ambiguities`, \
     `steps_used`, and `reason` (\"basis_budget\", \"word_len_budget\", or \
     \"step_budget\"). Nothing is claimed about the algebra; raise the limits \
     and rebuild."
);

create_exception!(
    auslander,
    DefectError,
    PyRuntimeError,
    "An internal cross-check of this library failed: a computation checked a \
     consequence of a theorem whose hypotheses hold, and the check came out \
    false. This is a bug in auslander, never bad input."
);

create_exception!(
    auslander,
    TransportInputError,
    PyValueError,
    "The map, homotopy, witness, or target term does not fit the supplied strict \
     transport inputs. The message and attached term or summand index identify \
     the failed precondition."
);

create_exception!(
    auslander,
    DerivedCertificateError,
    PyRuntimeError,
    "A checked condition of the derived-equivalence certificate failed. The \
     message and attached degree, dimension, term, or width identify that \
     condition."
);

create_exception!(
    auslander,
    CertificationBlockedError,
    PyRuntimeError,
    "A step could not be certified, so nothing downstream of it is claimed. \
     The three sources are an undetermined split, an undetermined \
     indecomposability gate, and an undecided isomorphism test inside the tau \
     cross-check. This is not budget exhaustion and raising a limit does not \
     help. A mutation walk reports the same condition as a value instead: \
     `IncompleteSupportTauTiltingGraph.reason` is then \
     \"certification_blocked\"."
);

create_exception!(
    auslander,
    NotIndecomposableError,
    PyValueError,
    "The module did not pass the indecomposability gate, which the \
     almost-split and category-radical constructions need. `kind` is \"zero\", \
     \"decomposable\", or \"undetermined\"; `summands` counts the certified \
     summands of a decomposable module and `attempts` the exhausted split \
     attempts of an undetermined one. Undetermined claims nothing either way."
);

create_exception!(
    auslander,
    IncompatibleSpacesError,
    PyValueError,
    "The two Ext classes do not live in one space, so the operation is \
     undefined. Compatible spaces need the same source module object, the \
     same target module object, and equal degrees. Comparison raises this \
     rather than answering False, which would claim the classes differ."
);

create_exception!(
    auslander,
    UnsupportedDomainError,
    PyValueError,
    "No complete enumeration of the indecomposables applies to this algebra, \
     so it has no AR quiver in this release. The message names both failed \
     routes, the Dynkin one and the Nakayama one."
);

create_exception!(
    auslander,
    ValuedArrowError,
    PyValueError,
    "The arrow is valued: a residue degree above 1 makes the dimensions of \
     Irr(X, Y) over the prime field and over the two residue fields differ, so \
     no single integer is the multiplicity. Read `base_field_dim`, \
     `dim_over_source_residue`, and `dim_over_target_residue`."
);

create_exception!(
    auslander,
    DynkinError,
    PyValueError,
    "A rejection of dynkin_indecomposables. The variant is the subclass, \
     NonzeroIdealError or NotDynkinError."
);

create_exception!(
    auslander,
    NonzeroIdealError,
    DynkinError,
    "The algebra is a proper quotient of kQ, so Gabriel's theorem does not list \
     its indecomposables. `forbidden_words` is the number of relations in the \
     reduced Groebner basis; for a monomial algebra these are exactly its \
     minimal forbidden words."
);

create_exception!(
    auslander,
    NotDynkinError,
    DynkinError,
    "The underlying graph of the quiver is no Dynkin diagram, so kQ is not \
     representation finite. `euclidean` is the EuclideanType of that graph when \
     it has one and None otherwise."
);
