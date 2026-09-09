//! Differential harness against QPA. Design notes in `tests/qpa-oracle/README.md`.
//!
//! The oracle is `tests/qpa-oracle/qpa_expected.json` (schema v9). Only a real
//! GAP+QPA run of `generate_fixtures.g` writes it. Every fixture carries its
//! own prime field and its full presentation. The harness rebuilds each algebra
//! from that presentation through `Relation`, `Presentation`, and
//! `Algebra::new`, so the library consumes the same input QPA saw. The
//! always-on test compares the library against the committed truth, and a
//! missing file is a hard failure. `native_snapshot.json` is a drift snapshot
//! of this library's own output, not an oracle. `QPA_ORACLE_WRITE=1` rewrites
//! the snapshot and never touches `qpa_expected.json`. `QPA_ORACLE=1` invokes
//! GAP itself and fails hard when GAP or QPA is unavailable, or when any value
//! disagrees.
//!
//! Two schema strings are implemented and no others: `SCHEMA` for the oracle,
//! and `SNAPSHOT_SCHEMA` for the snapshot, which is the v6 projection of this
//! library's values. The support tau-tilting block holds `brute_agreement`,
//! a GAP-internal cross-check with no library counterpart, so a snapshot at v9
//! would have to invent one.
//!
//! The JSON layer is hand-rolled. The schema is small and fixed, so a writer
//! built on `format!` and a strict recursive-descent reader replace a serde
//! dependency. The reader rejects unknown keys, duplicate keys, missing fields,
//! and malformed values, and cross-checks the oracle block against itself before
//! any of it is compared.

use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs;
#[cfg(unix)]
use std::path::Path;
use std::path::PathBuf;
#[cfg(unix)]
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex, OnceLock};

use auslander::algebra::Algebra;
use auslander::almost_split::{
    AlmostSplitOutcome, AlmostSplitWitness, almost_split, stable_hom as stable_hom_quotient,
};
use auslander::approx::left_approximation;
use auslander::ar::{tau, tau_via_nakayama_kernel};
use auslander::arquiver::{CatalogProvenance, IndecomposableCatalog};
use auslander::completion::CompletionLimits;
use auslander::decompose::{KrullSchmidtOutcome, krull_schmidt};
use auslander::ext::{ExtClass, ExtSpace, ext_dim, ext_table};
use auslander::field::{Fp, PrimeField};
use auslander::hom::{cokernel, hom_dim, kernel};
use auslander::indec::IndecomposableModule;
use auslander::injective::injective_dimension;
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::linalg::DenseMat;
use auslander::module::{Module, direct_sum};
use auslander::opposite::{OppositeMap, dual, opposite};
use auslander::quiver::{ArrowId, Quiver};
use auslander::radical::{radical, socle};
use auslander::relation::{Presentation, Relation};
use auslander::resolution::{Bounded, projective_dimension};
use auslander::supporttau::{SupportTauTiltingPair, enumerate_over_catalog};
use auslander::target::{TargetLimits, TargetPresentationOutcome, present_target};
use auslander::taugraph::{
    MutationGraphLimits, SupportTauTiltingGraphOutcome, support_tau_tilting_graph,
};
use auslander::taurigid::{TauRigidityOutcome, is_tau_rigid};
use auslander::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};

mod common;

/// The oracle document `qpa_expected.json`, written only by GAP+QPA.
const SCHEMA: &str = "auslander-qpa-oracle-v9";
/// `native_snapshot.json`, this library's own drift snapshot. It is the v6
/// projection of the library's values: every v6 field, and none of the v9
/// additions.
/// The support tau-tilting block contains `brute_agreement`, a GAP-internal
/// cross-check with no library counterpart, so a snapshot must not invent it.
const SNAPSHOT_SCHEMA: &str = "auslander-qpa-oracle-v6";
const MAX_EXT_DEGREE: usize = 4;
/// Projective and injective dimensions are recorded up to these bounds. A
/// simple whose dimension exceeds the bound is stored as `{"at_least": bound
/// + 1}`, the exact payload of the `Bounded::AtLeast` the library returns for
/// the same bound. QPA's `ProjDimensionOfModule` and `InjDimensionOfModule`
/// refuse the same way and return `false`.
const PROJDIM_BOUND: usize = 6;
const INJDIM_BOUND: usize = 6;
const ORDER_ID: &str = "deglex-arrowid-v1";
const DECOMPOSITION_MODULE: &str = "radicals-of-projectives";
const EXT_ALGEBRA_MODULE: &str = "sum-of-simples";

const ROOT_KEYS: [&str; 7] = [
    "schema",
    "convention",
    "max_ext_degree",
    "projdim_bound",
    "injdim_bound",
    "provenance",
    "fixtures",
];
const PROVENANCE_KEYS: [&str; 3] = ["gap_version", "qpa_version", "command"];
const FIXTURE_KEYS: [&str; 28] = [
    "family",
    "case",
    "field",
    "presentation_id",
    "ideal_id",
    "order",
    "quiver",
    "relations",
    "dim",
    "cartan",
    "injectives",
    "projdim",
    "injdim",
    "tau",
    "tau_injectives",
    "decomposition",
    "ext",
    "designated_modules",
    "ar_sequences",
    "irreducible_maps",
    "ext_algebra",
    "yoneda_products",
    "stable_hom",
    "tau_rigid",
    "rigid",
    "tau_period",
    "support_tau_tilting",
    "classical_tilting",
];

/// Keys of the v8 `support_tau_tilting` block on a fixture whose AR-quiver
/// walk closed, and on one whose walk did not. The closure marker decides
/// which set applies, so a document cannot carry a total without the marker
/// that admits it.
const STT_KEYS_CLOSED: [&str; 9] = [
    "indecomposables",
    "brute_agreement",
    "tau_rigid_designated",
    "total",
    "histogram",
    "pairs",
    "approximation_slots",
    "approximations",
    "exchange_graph_self_consistency",
];
const STT_KEYS_OPEN: [&str; 4] = [
    "indecomposables",
    "brute_agreement",
    "tau_rigid_designated",
    "not_computed",
];

/// The three classical-tilting records and the fixture that constructs each one.
const CLASSICAL_TILTING_MANIFEST: [(&str, &str, &str, &str, usize); 3] = [
    ("linear-an-3", "f5", "linear-a3-pd1", "S0+P0+P2", 1),
    ("a3-mod-ab", "f2", "a3-mod-ab-da-pd2", "I0+I1+I2", 2),
    ("a3-mod-ab", "f5", "a3-mod-ab-da-pd2", "I0+I1+I2", 2),
];

/// How many (pair, module summand) slots the generator samples per fixture.
const APPROX_SAMPLE: usize = 12;

/// The last stdout line of a completed generator run, printed after the write.
/// `gap -q -T` with closed stdin exits 0 after an uncaught error, so the exit
/// code is no signal and this line is what a live run checks.
const GENERATOR_SENTINEL: &str = "qpa-oracle-generator-ok";

/// What `generate_fixtures.g` writes into its working directory. It is not the
/// oracle's name, so an in-tree run cannot overwrite `qpa_expected.json`;
/// promoting a run is a deliberate copy.
const GENERATOR_OUTPUT: &str = "qpa_generated.json";

/// Every fixture shared by the v6 snapshot and v8 oracle, as (family, case).
/// A document that drops or renames one fails the comparison.
const FIXTURE_MANIFEST: [(&str, &str); 23] = [
    ("linear-an-2", "f5"),
    ("linear-an-3", "f5"),
    ("d4-star", "f5"),
    ("dual-numbers", "f5"),
    ("truncated-poly-3", "f5"),
    ("a3-mod-ab", "f5"),
    ("kronecker-2", "f5"),
    ("radical-square-zero-cycle-3", "f5"),
    ("linear-nakayama-3-2-1", "f5"),
    ("linear-nakayama-2-2-1", "f5"),
    ("cyclic-nakayama-3-3-3", "f5"),
    ("gentle-tree", "f5"),
    ("commutative-square", "f2"),
    ("commutative-square", "f5"),
    ("preprojective-a3", "f2"),
    ("preprojective-a3", "f3"),
    ("self-overlap", "f3"),
    ("inclusion-ambiguity", "f2"),
    ("inhomogeneous", "f5"),
    ("redundant-presentation", "f5"),
    ("permuted-presentation", "f5"),
    ("characteristic-sensitive", "f2"),
    ("characteristic-sensitive", "f3"),
];

/// The schema v8 fixture absent from the schema v6 native snapshot.
const V8_EXTRA_FIXTURES: [(&str, &str); 1] = [("a3-mod-ab", "f2")];

/// Minimal JSON reader for the oracle schema. Strict where corruption could
/// hide: duplicate object keys and trailing commas are parse errors. Only
/// whitespace is free-form. Numbers are integers with an optional sign, which
/// is all the schema needs; the only signed values are relation coefficients.
mod json {
    include!("qpa_oracle/json.rs");
}

include!("qpa_oracle/model.rs");

mod reader_primitives {
    use super::*;

    include!("qpa_oracle/reader_primitives.rs");
}

pub(crate) use reader_primitives::*;

mod reader_structures {
    use super::*;

    include!("qpa_oracle/reader_structures.rs");
}

pub(crate) use reader_structures::*;

mod reader_values {
    use super::*;

    include!("qpa_oracle/reader_values.rs");
}

pub(crate) use reader_values::*;

mod reader_document {
    use super::*;

    include!("qpa_oracle/reader_document.rs");
}

pub(crate) use reader_document::*;

mod compute {
    use super::*;

    include!("qpa_oracle/compute.rs");
}

pub(crate) use compute::*;

mod support_tau {
    use super::*;

    include!("qpa_oracle/support_tau.rs");
}

pub(crate) use support_tau::*;

mod compare_support {
    use super::*;

    include!("qpa_oracle/compare_support.rs");
}

pub(crate) use compare_support::*;

mod compare_target {
    use super::*;

    include!("qpa_oracle/compare_target.rs");
}

pub(crate) use compare_target::*;

mod compare_ar {
    use super::*;

    include!("qpa_oracle/compare_ar.rs");
}

pub(crate) use compare_ar::*;

mod compare_document {
    use super::*;

    include!("qpa_oracle/compare_document.rs");
}

pub(crate) use compare_document::*;

mod render {
    use super::*;

    include!("qpa_oracle/render.rs");
}

pub(crate) use render::*;

include!("qpa_oracle/tests_core.rs");

/// Corruption regressions: each mutation of the committed truth must be
/// caught, by the parser, by the strict reader, or by the comparator. Every
/// corruption target is asserted present in the committed bytes, so a test
/// cannot rot into replacing nothing.
mod corruption {
    use super::*;

    include!("qpa_oracle/corruption_a.rs");
    include!("qpa_oracle/corruption_b.rs");
}

mod census {
    include!("qpa_oracle/census.rs");
}
