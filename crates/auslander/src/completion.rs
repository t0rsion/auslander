//! Bergman-style completion for two-sided ideals in the path algebra.
//!
//! [`complete`] runs Buchberger/Bergman completion over the admissible
//! order [`crate::order::ORDER_ID`] and emits a [`crate::certificate::Certificate`] for the
//! independent verifier. The engine carries provenance through every
//! operation. Each certificate `origin` entry expands to its basis
//! element.
//!
//! Composition formulas, fixed for the engine and the certificate:
//!
//! - Overlap `(i, j, offset)`: the superposition word is `w = u·m·v` with
//!   `leading(g_i) = u·m`, `leading(g_j) = m·v`, `m` nonempty and proper
//!   on both sides, and `offset = |u|`. The composition is `g_i·v - u·g_j`.
//! - Inclusion `(i, j, offset)`: `leading(g_i) = u·leading(g_j)·v` with
//!   `leading(g_j)` a proper factor and `offset = |u|`. The composition is
//!   `g_i - u·g_j·v`.
//!
//! Canonical processing order: ambiguities live in a `BTreeSet` keyed
//! `(i, j, kind, offset)`, with overlap ordered before inclusion. The
//! engine drains the smallest key first. A new basis element enqueues its
//! ambiguities against every element, itself included, in both directions.
//! Every collection is deterministic, so identical input and limits
//! produce identical certificate bytes.
//!
//! The final basis is the unique reduced Groebner basis: monic elements,
//! and no leading word is a factor of any word of another element.
//! `membership` and `ambiguities` traces are recomputed against this
//! final basis, so the certificate is self-consistent.
//!
//! A normal word is a path that contains no leading word of the final
//! basis as a factor. `normal_words` lists every such word, in the fixed
//! basis order of the design, section 6: trivial paths in vertex order,
//! then length, then source, then the lexicographic arrow word. Each
//! emitted word costs one work unit of `max_steps`, so a huge finite
//! normal-word language truncates.
//!
//! Two sizes grow on their own budgets, because `max_steps` does not
//! bound them. Provenance compounds: one reduction step costs one unit
//! and adds up to the whole origin of the basis element it uses, so
//! `max_origin_terms` bounds each origin. Ambiguity enumeration is
//! quadratic in the basis and free of steps over a monomial ideal, where
//! every composition is exactly zero, so `max_ambiguities` bounds the
//! keys.
//!
//! `automaton` serializes the engine's normal-word automaton: one empty
//! word per vertex, then the proper nonempty leading-word prefixes sorted
//! lexicographically, with sparse `(state, arrow, next)` transitions
//! sorted by state then arrow. `finiteness` records the finiteness
//! decision. In the infinite case the engine extracts a `(prefix, cycle)`
//! witness from its own automaton and `normal_words` stays empty. The
//! verifier re-checks the automaton, the decision, and the witness.

mod automaton;
mod engine;
mod polynomial;
mod types;

use crate::quiver::{ArrowId, Quiver};

pub use types::{CompletionLimits, Outcome, TruncationDiagnostics, TruncationReason};

/// Completes `presentation` into the unique reduced Groebner basis of its
/// ideal and emits a certificate, or reports truncation when a budget of
/// `limits` runs out. See the module documentation for the composition
/// formulas, the processing order, and the `normal_words` contract.
pub fn complete(
    presentation: &crate::relation::Presentation,
    limits: &CompletionLimits,
) -> Outcome {
    engine::complete(presentation, limits)
}

/// Builds the shared normal-word automaton states and transitions.
///
/// `forbidden` must be factor-minimal. Then a prefix match cannot hide a
/// shorter forbidden suffix.
pub(crate) fn normal_word_transitions<W: AsRef<[ArrowId]>>(
    quiver: &Quiver,
    forbidden: &[W],
) -> (Vec<Vec<ArrowId>>, Vec<Vec<Option<usize>>>) {
    automaton::normal_word_transitions(quiver, forbidden)
}

#[cfg(test)]
mod tests;
