//! Bergman-style completion for two-sided ideals in the path algebra.
//!
//! [`complete`] runs plain Buchberger/Bergman completion over the sealed
//! order of [`crate::order`] and emits a [`Certificate`] for the
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
//! `normal_words` lists every word irreducible by the final leading
//! words, in the fixed basis order of the design, section 6: trivial
//! paths in vertex order, then length, then source, then the
//! lexicographic arrow word. Each emitted word costs one work unit of
//! `max_steps`, so a huge finite language truncates honestly.
//!
//! `automaton` serializes the engine's normal-word automaton: one empty
//! word per vertex, then the proper nonempty leading-word prefixes sorted
//! lexicographically, with sparse `(state, arrow, next)` transitions
//! sorted by state then arrow. `finiteness` records the finiteness
//! decision. In the infinite case the engine extracts a `(prefix, cycle)`
//! witness from its own automaton and `normal_words` stays empty. The
//! verifier re-checks the automaton, the decision, and the witness.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::certificate::{
    AmbiguityEntry, AmbiguityKind, AutomatonData, CERT_SCHEMA, Certificate, FinitenessData,
    OriginTerm, QuiverData, RelationData, Trace, TraceStep,
};
use crate::field::{Fp, PrimeField};
use crate::order::{ORDER_ID, word_cmp};
use crate::quiver::{ArrowId, Quiver};
use crate::relation::{Presentation, Relation};

/// Budgets for one completion run, each checked inside the reduction,
/// ambiguity, and emission loops.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompletionLimits {
    /// Maximum number of working-basis elements.
    pub max_basis: usize,
    /// Maximum arrow count of any input word or superposition word.
    pub max_word_len: usize,
    /// Maximum number of work units across the whole run. Each reduction
    /// step and each emitted normal word costs one unit. The budget is
    /// checked before the next word is allocated, so a huge finite
    /// normal-word language truncates instead of exhausting memory.
    pub max_steps: usize,
}

impl Default for CompletionLimits {
    /// The budgets sit far above the sizes this crate targets. A runaway
    /// completion still stops.
    fn default() -> Self {
        CompletionLimits {
            max_basis: 4096,
            max_word_len: 64,
            max_steps: 1_000_000,
        }
    }
}

/// Which budget of [`CompletionLimits`] ran out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TruncationReason {
    /// The working basis would exceed `max_basis`.
    BasisBudget,
    /// An input word or a superposition word exceeds `max_word_len`.
    WordLenBudget,
    /// The run needed more than `max_steps` work units.
    StepBudget,
}

/// Where a truncated run stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TruncationDiagnostics {
    /// Working basis size at the stop.
    pub basis_len: usize,
    /// Ambiguities that still need work at the stop. During completion
    /// this counts the queue plus the ambiguity in hand. During
    /// certificate emission it counts the traces not yet recorded; during
    /// normal-word emission every trace is recorded, so it is zero.
    pub pending_ambiguities: usize,
    /// Work units consumed before the stop: reduction steps plus emitted
    /// normal words.
    pub steps_used: usize,
    pub reason: TruncationReason,
}

/// Result of [`complete`]. A truncated outcome carries no certificate.
// An Outcome is built once and matched once, so the size gap between the
// variants never costs a hot copy.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(clippy::large_enum_variant)]
pub enum Outcome {
    Complete(Certificate),
    Truncated(TruncationDiagnostics),
}

type Word = Vec<ArrowId>;

/// Terms in strictly descending order under the sealed order.
#[derive(Clone, Debug)]
struct Poly {
    terms: Vec<(Fp, Word)>,
}

impl Poly {
    fn zero() -> Poly {
        Poly { terms: Vec::new() }
    }

    fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }
}

/// Provenance of a basis element: a map from `(input index, left word,
/// right word)` to a coefficient. The element equals `Σ c · u · r_i · v`.
type Origin = BTreeMap<(usize, Word, Word), Fp>;

#[derive(Clone, Debug)]
struct BasisElem {
    poly: Poly,
    origin: Origin,
}

fn lead_word(elem: &BasisElem) -> &Word {
    &elem.poly.terms[0].1
}

fn concat2(a: &[ArrowId], b: &[ArrowId]) -> Word {
    a.iter().chain(b).copied().collect()
}

fn concat3(a: &[ArrowId], b: &[ArrowId], c: &[ArrowId]) -> Word {
    a.iter().chain(b).chain(c).copied().collect()
}

fn raw_word(word: &[ArrowId]) -> Vec<u32> {
    word.iter().map(|a| a.0).collect()
}

fn poly_from_relation(relation: &Relation) -> Poly {
    Poly {
        terms: relation
            .terms()
            .iter()
            .map(|(c, w)| (*c, w.arrows().to_vec()))
            .collect(),
    }
}

fn poly_data(poly: &Poly) -> RelationData {
    poly.terms
        .iter()
        .map(|(c, w)| (c.raw(), raw_word(w)))
        .collect()
}

/// `base + c · left · src · right`, merged into strictly descending order.
/// Concatenation with a fixed context preserves the order on both sides,
/// so the mapped terms of `src` stay descending.
fn add_scaled(
    field: PrimeField,
    base: &Poly,
    c: Fp,
    left: &[ArrowId],
    src: &Poly,
    right: &[ArrowId],
) -> Poly {
    let addend: Vec<(Fp, Word)> = src
        .terms
        .iter()
        .map(|(k, w)| (field.mul(c, *k), concat3(left, w, right)))
        .collect();
    let mut merged = Vec::with_capacity(base.terms.len() + addend.len());
    let mut i = 0;
    let mut j = 0;
    while i < base.terms.len() && j < addend.len() {
        match word_cmp(&base.terms[i].1, &addend[j].1) {
            Ordering::Greater => {
                merged.push(base.terms[i].clone());
                i += 1;
            }
            Ordering::Less => {
                merged.push(addend[j].clone());
                j += 1;
            }
            Ordering::Equal => {
                let sum = field.add(base.terms[i].0, addend[j].0);
                if !sum.is_zero() {
                    merged.push((sum, base.terms[i].1.clone()));
                }
                i += 1;
                j += 1;
            }
        }
    }
    merged.extend_from_slice(&base.terms[i..]);
    merged.extend(addend.into_iter().skip(j));
    Poly { terms: merged }
}

/// `target += c · left · src · right` on provenance, dropping zero sums.
fn origin_add_scaled(
    field: PrimeField,
    target: &mut Origin,
    c: Fp,
    left: &[ArrowId],
    src: &Origin,
    right: &[ArrowId],
) {
    for ((index, l, r), k) in src {
        let key = (*index, concat2(left, l), concat2(r, right));
        let current = target.get(&key).copied().unwrap_or(field.zero());
        let sum = field.add(current, field.mul(c, *k));
        if sum.is_zero() {
            target.remove(&key);
        } else {
            target.insert(key, sum);
        }
    }
}

fn make_monic(field: PrimeField, poly: &mut Poly, origin: &mut Origin) {
    let lead_coeff = poly.terms[0].0;
    if lead_coeff == field.one() {
        return;
    }
    let inv = field.inv(lead_coeff);
    for (c, _) in &mut poly.terms {
        *c = field.mul(inv, *c);
    }
    for c in origin.values_mut() {
        *c = field.mul(inv, *c);
    }
}

/// Leftmost occurrence of `pattern` inside `word`.
fn find_factor(word: &[ArrowId], pattern: &[ArrowId]) -> Option<usize> {
    if pattern.len() > word.len() {
        return None;
    }
    (0..=word.len() - pattern.len()).find(|&start| word[start..start + pattern.len()] == *pattern)
}

/// The next reduction target: `(term index, basis index, position)` for
/// the largest reducible word, the lowest reducing basis index, and its
/// leftmost occurrence. `skip` excludes one basis element.
fn find_reduction(
    basis: &[BasisElem],
    skip: Option<usize>,
    poly: &Poly,
) -> Option<(usize, usize, usize)> {
    for (term_index, (_, word)) in poly.terms.iter().enumerate() {
        for (basis_index, elem) in basis.iter().enumerate() {
            if skip == Some(basis_index) {
                continue;
            }
            if let Some(position) = find_factor(word, lead_word(elem)) {
                return Some((term_index, basis_index, position));
            }
        }
    }
    None
}

const KIND_OVERLAP: u8 = 0;
const KIND_INCLUSION: u8 = 1;

/// Canonical ambiguity key `(i, j, kind, offset)`. Overlap sorts before
/// inclusion.
type AmbKey = (usize, usize, u8, usize);

/// All ambiguities of the ordered pair `(i, j)` with leading words
/// `li`, `lj`. Overlap: a proper nonempty suffix of `li` equals a proper
/// nonempty prefix of `lj`; `offset` is where `lj` starts inside the
/// superposition word. Inclusion: `lj` is a proper factor of `li` at
/// `offset`.
fn pair_ambiguities(
    i: usize,
    j: usize,
    li: &[ArrowId],
    lj: &[ArrowId],
    out: &mut BTreeSet<AmbKey>,
) {
    for k in 1..li.len().min(lj.len()) {
        if li[li.len() - k..] == lj[..k] {
            out.insert((i, j, KIND_OVERLAP, li.len() - k));
        }
    }
    if lj.len() < li.len() {
        for offset in 0..=li.len() - lj.len() {
            if li[offset..offset + lj.len()] == *lj {
                out.insert((i, j, KIND_INCLUSION, offset));
            }
        }
    }
}

fn superposition_len(basis: &[BasisElem], key: AmbKey) -> usize {
    let (i, j, kind, offset) = key;
    if kind == KIND_OVERLAP {
        offset + lead_word(&basis[j]).len()
    } else {
        let _ = j;
        lead_word(&basis[i]).len()
    }
}

struct StepsExhausted;

struct Engine<'a> {
    field: PrimeField,
    limits: &'a CompletionLimits,
    steps: usize,
}

impl Engine<'_> {
    fn diag(
        &self,
        basis_len: usize,
        pending_ambiguities: usize,
        reason: TruncationReason,
    ) -> TruncationDiagnostics {
        TruncationDiagnostics {
            basis_len,
            pending_ambiguities,
            steps_used: self.steps,
            reason,
        }
    }

    /// Full remainder division of `poly` by `basis`, excluding `skip`.
    /// Each step takes the largest reducible word, the lowest reducing
    /// basis index, and its leftmost occurrence. The step subtracts
    /// `c · left · basis[k] · right`, where `c` is the current
    /// coefficient of the word. Every step strictly decreases the word
    /// multiset in the sealed order, so the loop terminates.
    fn reduce_full(
        &mut self,
        basis: &[BasisElem],
        skip: Option<usize>,
        poly: &mut Poly,
        mut origin: Option<&mut Origin>,
        mut trace: Option<&mut Vec<TraceStep>>,
    ) -> Result<(), StepsExhausted> {
        loop {
            let Some((term_index, basis_index, position)) = find_reduction(basis, skip, poly)
            else {
                return Ok(());
            };
            if self.steps >= self.limits.max_steps {
                return Err(StepsExhausted);
            }
            self.steps += 1;
            let (coeff, word) = poly.terms[term_index].clone();
            let lead_len = lead_word(&basis[basis_index]).len();
            let left = word[..position].to_vec();
            let right = word[position + lead_len..].to_vec();
            if let Some(steps) = trace.as_deref_mut() {
                steps.push(TraceStep {
                    word: raw_word(&word),
                    basis_index,
                    left: raw_word(&left),
                    right: raw_word(&right),
                    coeff: coeff.raw(),
                });
            }
            let neg = self.field.neg(coeff);
            *poly = add_scaled(
                self.field,
                poly,
                neg,
                &left,
                &basis[basis_index].poly,
                &right,
            );
            if let Some(target) = origin.as_deref_mut() {
                origin_add_scaled(
                    self.field,
                    target,
                    neg,
                    &left,
                    &basis[basis_index].origin,
                    &right,
                );
            }
        }
    }

    /// The composition polynomial and provenance for `key`. Overlap:
    /// `g_i·v - u·g_j`. Inclusion: `g_i - u·g_j·v`.
    fn composition(&self, basis: &[BasisElem], key: AmbKey) -> (Poly, Origin) {
        let (i, j, kind, offset) = key;
        let li = lead_word(&basis[i]).clone();
        let lj = lead_word(&basis[j]).clone();
        let neg_one = self.field.neg(self.field.one());
        let (u, v): (&[ArrowId], &[ArrowId]) = if kind == KIND_OVERLAP {
            (&li[..offset], &lj[li.len() - offset..])
        } else {
            (&li[..offset], &li[offset + lj.len()..])
        };
        let mut poly;
        let mut origin;
        if kind == KIND_OVERLAP {
            poly = add_scaled(
                self.field,
                &Poly::zero(),
                self.field.one(),
                &[],
                &basis[i].poly,
                v,
            );
            origin = Origin::new();
            origin_add_scaled(
                self.field,
                &mut origin,
                self.field.one(),
                &[],
                &basis[i].origin,
                v,
            );
            poly = add_scaled(self.field, &poly, neg_one, u, &basis[j].poly, &[]);
            origin_add_scaled(self.field, &mut origin, neg_one, u, &basis[j].origin, &[]);
        } else {
            poly = basis[i].poly.clone();
            origin = basis[i].origin.clone();
            poly = add_scaled(self.field, &poly, neg_one, u, &basis[j].poly, v);
            origin_add_scaled(self.field, &mut origin, neg_one, u, &basis[j].origin, v);
        }
        (poly, origin)
    }

    /// Drops every element whose leading word contains another element's
    /// leading word as a factor, sorts the rest by leading word, and
    /// reduces each element's tail by the others. Returns the reduced
    /// basis and whether the leading-word set changed.
    fn interreduce(
        &mut self,
        basis: Vec<BasisElem>,
    ) -> Result<(Vec<BasisElem>, bool), TruncationDiagnostics> {
        let mut kept: Vec<BasisElem> = Vec::new();
        for (i, elem) in basis.iter().enumerate() {
            let redundant = basis.iter().enumerate().any(|(j, other)| {
                j != i && find_factor(lead_word(elem), lead_word(other)).is_some()
            });
            if !redundant {
                kept.push(elem.clone());
            }
        }
        let dropped = kept.len() != basis.len();
        kept.sort_by(|a, b| word_cmp(lead_word(a), lead_word(b)));
        for index in 0..kept.len() {
            let mut elem = kept[index].clone();
            if self
                .reduce_full(
                    &kept,
                    Some(index),
                    &mut elem.poly,
                    Some(&mut elem.origin),
                    None,
                )
                .is_err()
            {
                return Err(self.diag(kept.len(), 0, TruncationReason::StepBudget));
            }
            kept[index] = elem;
        }
        Ok((kept, dropped))
    }

    fn emit(
        &mut self,
        presentation: &Presentation,
        basis: &[BasisElem],
    ) -> Result<Certificate, TruncationDiagnostics> {
        let mut keys: BTreeSet<AmbKey> = BTreeSet::new();
        for i in 0..basis.len() {
            for j in 0..basis.len() {
                pair_ambiguities(i, j, lead_word(&basis[i]), lead_word(&basis[j]), &mut keys);
            }
        }
        let input_relations: Vec<RelationData> = presentation
            .relations()
            .iter()
            .map(|r| poly_data(&poly_from_relation(r)))
            .collect();
        let mut membership = Vec::with_capacity(input_relations.len());
        for relation in presentation.relations() {
            let mut poly = poly_from_relation(relation);
            let start = poly_data(&poly);
            let mut steps = Vec::new();
            if self
                .reduce_full(basis, None, &mut poly, None, Some(&mut steps))
                .is_err()
            {
                return Err(self.diag(basis.len(), keys.len(), TruncationReason::StepBudget));
            }
            debug_assert!(
                poly.is_zero(),
                "input relation must reduce to zero over the final basis"
            );
            membership.push(Trace { start, steps });
        }
        let total = keys.len();
        let mut ambiguities = Vec::with_capacity(total);
        for (done, &key) in keys.iter().enumerate() {
            let (mut poly, _) = self.composition(basis, key);
            let start = poly_data(&poly);
            let mut steps = Vec::new();
            if self
                .reduce_full(basis, None, &mut poly, None, Some(&mut steps))
                .is_err()
            {
                return Err(self.diag(basis.len(), total - done, TruncationReason::StepBudget));
            }
            debug_assert!(
                poly.is_zero(),
                "composition must reduce to zero over the final basis"
            );
            let (i, j, kind, offset) = key;
            ambiguities.push(AmbiguityEntry {
                i,
                j,
                kind: if kind == KIND_OVERLAP {
                    AmbiguityKind::Overlap
                } else {
                    AmbiguityKind::Inclusion
                },
                offset,
                trace: Trace { start, steps },
            });
        }
        let leads: Vec<&Word> = basis.iter().map(lead_word).collect();
        let quiver = presentation.quiver();
        let automaton = PrefixAutomaton::build(quiver, &leads);
        let (finiteness, normal_words) = match automaton.cycle_witness() {
            Some((prefix, cycle)) => (FinitenessData::Infinite { prefix, cycle }, Vec::new()),
            None => (
                FinitenessData::Finite,
                self.normal_words(quiver, &automaton, basis.len())?,
            ),
        };
        Ok(Certificate {
            schema: CERT_SCHEMA.to_string(),
            field: self.field.modulus(),
            quiver: QuiverData {
                vertices: quiver.num_vertices(),
                arrows: quiver.arrows().to_vec(),
            },
            order: ORDER_ID.to_string(),
            input_relations,
            basis: basis.iter().map(|e| poly_data(&e.poly)).collect(),
            origin: basis.iter().map(origin_terms).collect(),
            membership,
            ambiguities,
            normal_words,
            automaton: automaton.data(),
            finiteness,
        })
    }

    /// All words irreducible by the final leading words, in the fixed
    /// basis order. Each emitted word costs one work unit, checked before
    /// the word is allocated.
    fn normal_words(
        &mut self,
        quiver: &Quiver,
        automaton: &PrefixAutomaton,
        basis_len: usize,
    ) -> Result<Vec<Vec<u32>>, TruncationDiagnostics> {
        let mut rows: Vec<(u32, u32, Word)> = Vec::new();
        let mut states: Vec<usize> = Vec::new();
        for v in 0..quiver.num_vertices() {
            if self.steps >= self.limits.max_steps {
                return Err(self.diag(basis_len, 0, TruncationReason::StepBudget));
            }
            self.steps += 1;
            rows.push((v, v, Vec::new()));
            states.push(v as usize);
        }
        let mut level_start = 0;
        while level_start < rows.len() {
            let level_end = rows.len();
            for i in level_start..level_end {
                let (source, target, word) = rows[i].clone();
                let s = states[i];
                for &a in quiver.arrows_from(target) {
                    if let Some(next) = automaton.step(s, a) {
                        if self.steps >= self.limits.max_steps {
                            return Err(self.diag(basis_len, 0, TruncationReason::StepBudget));
                        }
                        self.steps += 1;
                        let mut extended = word.clone();
                        extended.push(a);
                        rows.push((source, quiver.target(a), extended));
                        states.push(next);
                    }
                }
            }
            level_start = level_end;
        }
        rows.sort_by(|(sa, _, wa), (sb, _, wb)| {
            wa.len().cmp(&wb.len()).then(sa.cmp(sb)).then(wa.cmp(wb))
        });
        Ok(rows.into_iter().map(|(_, _, w)| raw_word(&w)).collect())
    }
}

fn origin_terms(elem: &BasisElem) -> Vec<OriginTerm> {
    elem.origin
        .iter()
        .map(|((index, left, right), coeff)| OriginTerm {
            coeff: coeff.raw(),
            left: raw_word(left),
            input_index: *index,
            right: raw_word(right),
        })
        .collect()
}

/// Completes `presentation` into the unique reduced Groebner basis of its
/// ideal and emits a certificate, or reports honest truncation when a
/// budget of `limits` runs out. See the module documentation for the
/// composition formulas, the processing order, and the `normal_words`
/// contract.
pub fn complete(presentation: &Presentation, limits: &CompletionLimits) -> Outcome {
    match run(presentation, limits) {
        Ok(certificate) => Outcome::Complete(certificate),
        Err(diagnostics) => Outcome::Truncated(diagnostics),
    }
}

fn run(
    presentation: &Presentation,
    limits: &CompletionLimits,
) -> Result<Certificate, TruncationDiagnostics> {
    let mut engine = Engine {
        field: presentation.field(),
        limits,
        steps: 0,
    };
    let mut basis: Vec<BasisElem> = Vec::new();
    for (index, relation) in presentation.relations().iter().enumerate() {
        if relation.leading().1.len() > limits.max_word_len {
            return Err(engine.diag(basis.len(), 0, TruncationReason::WordLenBudget));
        }
        let mut poly = poly_from_relation(relation);
        let mut origin = Origin::new();
        origin.insert((index, Vec::new(), Vec::new()), engine.field.one());
        if engine
            .reduce_full(&basis, None, &mut poly, Some(&mut origin), None)
            .is_err()
        {
            return Err(engine.diag(basis.len(), 0, TruncationReason::StepBudget));
        }
        if poly.is_zero() {
            continue;
        }
        if basis.len() >= limits.max_basis {
            return Err(engine.diag(basis.len(), 0, TruncationReason::BasisBudget));
        }
        make_monic(engine.field, &mut poly, &mut origin);
        basis.push(BasisElem { poly, origin });
    }
    loop {
        let mut queue: BTreeSet<AmbKey> = BTreeSet::new();
        for i in 0..basis.len() {
            for j in 0..basis.len() {
                pair_ambiguities(i, j, lead_word(&basis[i]), lead_word(&basis[j]), &mut queue);
            }
        }
        while let Some(key) = queue.pop_first() {
            let pending = queue.len() + 1;
            if superposition_len(&basis, key) > limits.max_word_len {
                return Err(engine.diag(basis.len(), pending, TruncationReason::WordLenBudget));
            }
            let (mut poly, mut origin) = engine.composition(&basis, key);
            if engine
                .reduce_full(&basis, None, &mut poly, Some(&mut origin), None)
                .is_err()
            {
                return Err(engine.diag(basis.len(), pending, TruncationReason::StepBudget));
            }
            if poly.is_zero() {
                continue;
            }
            if basis.len() >= limits.max_basis {
                return Err(engine.diag(basis.len(), pending, TruncationReason::BasisBudget));
            }
            make_monic(engine.field, &mut poly, &mut origin);
            basis.push(BasisElem { poly, origin });
            let new = basis.len() - 1;
            for other in 0..basis.len() {
                pair_ambiguities(
                    new,
                    other,
                    lead_word(&basis[new]),
                    lead_word(&basis[other]),
                    &mut queue,
                );
                pair_ambiguities(
                    other,
                    new,
                    lead_word(&basis[other]),
                    lead_word(&basis[new]),
                    &mut queue,
                );
            }
        }
        let (reduced, dropped) = engine.interreduce(basis)?;
        basis = reduced;
        if !dropped {
            break;
        }
    }
    engine.emit(presentation, &basis)
}

/// The irreducible-prefix automaton over the final leading words.
/// States `0..n` are the vertices. The rest are the proper nonempty
/// prefixes of leading words, sorted lexicographically. Reading an
/// irreducible word from its source-vertex state ends in the state of its
/// longest tracked suffix. A forbidden factor leaves no transition.
struct PrefixAutomaton {
    /// The word of each state; empty for the start states.
    words: Vec<Word>,
    trans: Vec<Vec<Option<usize>>>,
    starts: usize,
}

impl PrefixAutomaton {
    fn build(quiver: &Quiver, forbidden: &[&Word]) -> PrefixAutomaton {
        let n = quiver.num_vertices() as usize;
        let mut prefix_set: BTreeSet<Word> = BTreeSet::new();
        for word in forbidden {
            for len in 1..word.len() {
                prefix_set.insert(word[..len].to_vec());
            }
        }
        let mut words: Vec<Word> = vec![Word::new(); n];
        let mut prefix_index: BTreeMap<Word, usize> = BTreeMap::new();
        for prefix in prefix_set {
            prefix_index.insert(prefix.clone(), words.len());
            words.push(prefix);
        }
        let forbidden_set: BTreeSet<&[ArrowId]> = forbidden.iter().map(|w| w.as_slice()).collect();
        let mut trans = vec![vec![None; quiver.num_arrows()]; words.len()];
        for (s, row) in trans.iter_mut().enumerate() {
            let (word, vertex): (&[ArrowId], u32) = if s < n {
                (&[], s as u32)
            } else {
                let w = words[s].as_slice();
                (w, quiver.target(w[w.len() - 1]))
            };
            for &a in quiver.arrows_from(vertex) {
                let mut extended = word.to_vec();
                extended.push(a);
                // The longest suffix in (forbidden ∪ prefixes) decides.
                // The leading words of a reduced basis are minimal, so
                // the two sets are disjoint and no shorter forbidden
                // suffix hides under a prefix match.
                let mut next = Some(quiver.target(a) as usize);
                for start in 0..extended.len() {
                    let suffix = &extended[start..];
                    if forbidden_set.contains(suffix) {
                        next = None;
                        break;
                    }
                    if let Some(&k) = prefix_index.get(suffix) {
                        next = Some(k);
                        break;
                    }
                }
                row[a.index()] = next;
            }
        }
        PrefixAutomaton {
            words,
            trans,
            starts: n,
        }
    }

    /// The automaton as certificate data: state words in state order,
    /// sparse transition triples sorted by state then arrow.
    fn data(&self) -> AutomatonData {
        let states = self.words.iter().map(|w| raw_word(w)).collect();
        let mut transitions = Vec::new();
        for (state, row) in self.trans.iter().enumerate() {
            for (arrow, next) in row.iter().enumerate() {
                if let Some(next) = next {
                    transitions.push((state, arrow as u32, *next));
                }
            }
        }
        AutomatonData {
            states,
            transitions,
        }
    }

    /// A `(prefix, cycle)` word witness when the reachable part of the
    /// automaton has a cycle; `None` when it is acyclic, so the language
    /// is finite. The prefix reads from the start state of its source
    /// vertex to a state on the cycle, and the cycle returns to exactly
    /// that state, so every step follows an automaton edge and the whole
    /// walk spells an irreducible word.
    fn cycle_witness(&self) -> Option<(Vec<u32>, Vec<u32>)> {
        let m = self.trans.len();
        let mut reachable = vec![false; m];
        let mut parent: Vec<Option<(usize, u32)>> = vec![None; m];
        let mut queue: VecDeque<usize> = (0..self.starts).collect();
        reachable[..self.starts].fill(true);
        while let Some(state) = queue.pop_front() {
            for (arrow, next) in self.trans[state].iter().enumerate() {
                let Some(next) = *next else { continue };
                if !reachable[next] {
                    reachable[next] = true;
                    parent[next] = Some((state, arrow as u32));
                    queue.push_back(next);
                }
            }
        }
        let mut out_degree = vec![0usize; m];
        let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); m];
        for state in 0..m {
            if !reachable[state] {
                continue;
            }
            for &next in self.trans[state].iter().flatten() {
                out_degree[state] += 1;
                predecessors[next].push(state);
            }
        }
        let mut removed = vec![false; m];
        let mut ready: VecDeque<usize> = (0..m)
            .filter(|&state| reachable[state] && out_degree[state] == 0)
            .collect();
        while let Some(state) = ready.pop_front() {
            removed[state] = true;
            for &before in &predecessors[state] {
                out_degree[before] -= 1;
                if out_degree[before] == 0 {
                    ready.push_back(before);
                }
            }
        }
        let live = |state: usize| reachable[state] && !removed[state];
        let start = (0..m).find(|&state| live(state))?;
        let mut position = BTreeMap::new();
        let mut walk: Vec<u32> = Vec::new();
        let mut current = start;
        let (entry, cycle_state) = loop {
            if let Some(&at) = position.get(&current) {
                break (at, current);
            }
            position.insert(current, walk.len());
            let (arrow, next) = self.trans[current]
                .iter()
                .enumerate()
                .find_map(|(arrow, next)| next.filter(|&t| live(t)).map(|t| (arrow as u32, t)))
                .expect("a state that survives pruning keeps a surviving successor");
            walk.push(arrow);
            current = next;
        };
        let cycle = walk[entry..].to_vec();
        let mut prefix = Vec::new();
        let mut state = cycle_state;
        while let Some((before, arrow)) = parent[state] {
            prefix.push(arrow);
            state = before;
        }
        prefix.reverse();
        Some((prefix, cycle))
    }

    #[inline]
    fn step(&self, state: usize, arrow: ArrowId) -> Option<usize> {
        self.trans[state][arrow.index()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(p: u64) -> PrimeField {
        PrimeField::new(p).unwrap()
    }

    fn ids(raw: &[u32]) -> Vec<ArrowId> {
        raw.iter().copied().map(ArrowId).collect()
    }

    fn rel(quiver: &Quiver, field: PrimeField, terms: &[(i64, &[u32])]) -> Relation {
        Relation::new(
            quiver,
            field,
            terms
                .iter()
                .map(|(c, w)| (field.elem(*c), ids(w)))
                .collect(),
        )
        .unwrap()
    }

    fn completed(presentation: &Presentation) -> Certificate {
        match complete(presentation, &CompletionLimits::default()) {
            Outcome::Complete(certificate) => certificate,
            Outcome::Truncated(diagnostics) => panic!("unexpected truncation: {diagnostics:?}"),
        }
    }

    fn truncated(presentation: &Presentation, limits: &CompletionLimits) -> TruncationDiagnostics {
        match complete(presentation, limits) {
            Outcome::Complete(_) => panic!("expected truncation"),
            Outcome::Truncated(diagnostics) => diagnostics,
        }
    }

    fn x_cubed() -> Presentation {
        let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
        let field = f(5);
        let r = rel(&quiver, field, &[(1, &[0, 0, 0])]);
        Presentation::new(quiver, field, vec![r]).unwrap()
    }

    fn commutative_square() -> Presentation {
        let quiver = Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).unwrap();
        let field = f(5);
        let r = rel(&quiver, field, &[(1, &[0, 1]), (-1, &[2, 3])]);
        Presentation::new(quiver, field, vec![r]).unwrap()
    }

    /// One vertex, loops x = 0 and y = 1, over F_2. Relations
    /// r0 = yx - x² and r1 = y².
    fn overlap_example() -> Presentation {
        let quiver = Quiver::new(1, &[(0, 0), (0, 0)]).unwrap();
        let field = f(2);
        let r0 = rel(&quiver, field, &[(1, &[1, 0]), (-1, &[0, 0])]);
        let r1 = rel(&quiver, field, &[(1, &[1, 1])]);
        Presentation::new(quiver, field, vec![r0, r1]).unwrap()
    }

    fn overlap_example_swapped() -> Presentation {
        let quiver = Quiver::new(1, &[(0, 0), (0, 0)]).unwrap();
        let field = f(2);
        let r0 = rel(&quiver, field, &[(1, &[1, 0]), (-1, &[0, 0])]);
        let r1 = rel(&quiver, field, &[(1, &[1, 1])]);
        Presentation::new(quiver, field, vec![r1, r0]).unwrap()
    }

    /// Arrows a: 0->1 (0), b: 1->3 (1), c: 0->2 (2), d: 2->4 (3),
    /// e: 4->3 (4). The relation cde - ab mixes word lengths 3 and 2.
    fn inhomogeneous() -> Presentation {
        let quiver = Quiver::new(5, &[(0, 1), (1, 3), (0, 2), (2, 4), (4, 3)]).unwrap();
        let field = f(5);
        let r = rel(&quiver, field, &[(1, &[2, 3, 4]), (-1, &[0, 1])]);
        Presentation::new(quiver, field, vec![r]).unwrap()
    }

    /// One loop x over F_2. Relations r0 = x⁵ and r1 = x⁴ + x². The ideal
    /// is (x²): the inclusion of x⁴ in x⁵ and the overlaps produce x³ and
    /// x². Interreduction drops everything else.
    fn inclusion_example() -> Presentation {
        let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
        let field = f(2);
        let r0 = rel(&quiver, field, &[(1, &[0, 0, 0, 0, 0])]);
        let r1 = rel(&quiver, field, &[(1, &[0, 0, 0, 0]), (1, &[0, 0])]);
        Presentation::new(quiver, field, vec![r0, r1]).unwrap()
    }

    fn one_loop_free() -> Presentation {
        let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
        Presentation::new(quiver, f(2), Vec::new()).unwrap()
    }

    fn all_examples() -> Vec<Presentation> {
        vec![
            x_cubed(),
            commutative_square(),
            overlap_example(),
            overlap_example_swapped(),
            inhomogeneous(),
            inclusion_example(),
            one_loop_free(),
        ]
    }

    /// Naive expansion of one origin: `Σ coeff · left · r_i · right`,
    /// collected per word, zeros dropped, sorted descending.
    fn expand_origin(
        field: PrimeField,
        inputs: &[RelationData],
        origin: &[OriginTerm],
    ) -> RelationData {
        let mut acc: BTreeMap<Vec<u32>, Fp> = BTreeMap::new();
        for term in origin {
            let c = field.elem(term.coeff as i64);
            for (rc, rw) in &inputs[term.input_index] {
                let mut word = term.left.clone();
                word.extend_from_slice(rw);
                word.extend_from_slice(&term.right);
                let add = field.mul(c, field.elem(*rc as i64));
                let sum = field.add(acc.get(&word).copied().unwrap_or(field.zero()), add);
                if sum.is_zero() {
                    acc.remove(&word);
                } else {
                    acc.insert(word, sum);
                }
            }
        }
        let mut expanded: Vec<(u64, Vec<u32>)> =
            acc.into_iter().map(|(w, c)| (c.raw(), w)).collect();
        expanded.sort_by(|(_, a), (_, b)| b.len().cmp(&a.len()).then(b.cmp(a)));
        expanded
    }

    /// Replays a trace with its own arithmetic: checks every step's word
    /// decomposition and that the final value is zero.
    fn assert_trace_reduces_to_zero(field: PrimeField, basis: &[RelationData], trace: &Trace) {
        let mut acc: BTreeMap<Vec<u32>, Fp> = BTreeMap::new();
        for (c, w) in &trace.start {
            assert!(acc.insert(w.clone(), field.elem(*c as i64)).is_none());
        }
        for step in &trace.steps {
            let elem = &basis[step.basis_index];
            let mut recomposed = step.left.clone();
            recomposed.extend_from_slice(&elem[0].1);
            recomposed.extend_from_slice(&step.right);
            assert_eq!(step.word, recomposed);
            let c = field.elem(step.coeff as i64);
            for (bc, bw) in elem {
                let mut word = step.left.clone();
                word.extend_from_slice(bw);
                word.extend_from_slice(&step.right);
                let sub = field.mul(c, field.elem(*bc as i64));
                let sum = field.sub(acc.get(&word).copied().unwrap_or(field.zero()), sub);
                if sum.is_zero() {
                    acc.remove(&word);
                } else {
                    acc.insert(word, sum);
                }
            }
        }
        assert!(acc.is_empty(), "trace does not end at zero: {acc:?}");
    }

    #[test]
    fn monomial_x_cubed_is_a_no_op() {
        let c = completed(&x_cubed());
        assert_eq!(c.schema, CERT_SCHEMA);
        assert_eq!(c.field, 5);
        assert_eq!(c.order, ORDER_ID);
        assert_eq!(
            c.quiver,
            QuiverData {
                vertices: 1,
                arrows: vec![(0, 0)],
            }
        );
        assert_eq!(c.input_relations, vec![vec![(1, vec![0, 0, 0])]]);
        assert_eq!(c.basis, vec![vec![(1, vec![0, 0, 0])]]);
        assert_eq!(
            c.origin,
            vec![vec![OriginTerm {
                coeff: 1,
                left: vec![],
                input_index: 0,
                right: vec![],
            }]]
        );
        assert_eq!(
            c.membership,
            vec![Trace {
                start: vec![(1, vec![0, 0, 0])],
                steps: vec![TraceStep {
                    word: vec![0, 0, 0],
                    basis_index: 0,
                    left: vec![],
                    right: vec![],
                    coeff: 1,
                }],
            }]
        );
        // Self-overlaps of xxx: the shared part is xx (offset 1) or x
        // (offset 2). Both compositions are zero, so the traces are
        // empty.
        assert_eq!(c.ambiguities.len(), 2);
        for (entry, offset) in c.ambiguities.iter().zip([1usize, 2]) {
            assert_eq!(
                (entry.i, entry.j, entry.kind, entry.offset),
                (0, 0, AmbiguityKind::Overlap, offset)
            );
            assert_eq!(
                entry.trace,
                Trace {
                    start: vec![],
                    steps: vec![],
                }
            );
        }
        assert_eq!(c.normal_words, vec![vec![], vec![0], vec![0, 0]]);
        // States: the vertex, then the proper prefixes x and xx of the
        // leading word xxx. Reading x from a state advances one prefix;
        // xx has no transition because xxx is forbidden.
        assert_eq!(
            c.automaton,
            AutomatonData {
                states: vec![vec![], vec![0], vec![0, 0]],
                transitions: vec![(0, 0, 1), (1, 0, 2)],
            }
        );
        assert_eq!(c.finiteness, FinitenessData::Finite);
    }

    #[test]
    fn commutative_square_rewrites_cd_to_ab() {
        let c = completed(&commutative_square());
        // Input ab - cd is stored descending as 4·cd + ab. Monic scaling
        // by inv(4) = 4 gives cd + 4·ab, the rule cd -> ab.
        assert_eq!(
            c.input_relations,
            vec![vec![(4, vec![2, 3]), (1, vec![0, 1])]]
        );
        assert_eq!(c.basis, vec![vec![(1, vec![2, 3]), (4, vec![0, 1])]]);
        assert_eq!(
            c.origin,
            vec![vec![OriginTerm {
                coeff: 4,
                left: vec![],
                input_index: 0,
                right: vec![],
            }]]
        );
        assert_eq!(
            c.membership,
            vec![Trace {
                start: vec![(4, vec![2, 3]), (1, vec![0, 1])],
                steps: vec![TraceStep {
                    word: vec![2, 3],
                    basis_index: 0,
                    left: vec![],
                    right: vec![],
                    coeff: 4,
                }],
            }]
        );
        assert!(c.ambiguities.is_empty());
        // Fixed basis order: e_0..e_3, then length 1 by (source, word):
        // a (source 0), c (source 0), b (source 1), d (source 2), then ab.
        assert_eq!(
            c.normal_words,
            vec![
                vec![],
                vec![],
                vec![],
                vec![],
                vec![0],
                vec![2],
                vec![1],
                vec![3],
                vec![0, 1],
            ]
        );
        assert_eq!(c.normal_words.len(), 9);
    }

    /// Hand computation for `overlap_example` (F_2, x = 0, y = 1):
    /// seeds g0 = yx + xx, g1 = yy. The only initial ambiguities are the
    /// overlap of yy with yx (suffix y = prefix y) and the self-overlap
    /// of yy. The first composition is g1·x - y·g0 = yyx - yyx - yxx =
    /// yxx. Reduction by g0 at position 0 leaves xxx. That word is
    /// irreducible, so g2 = xxx joins the basis. All later compositions
    /// reduce to zero, and interreduction changes nothing. The reduced
    /// basis is {yx + xx, yy, xxx} and the normal words are
    /// {e, x, y, xx, xy, xxy}.
    #[test]
    fn overlap_completion_adds_xxx() {
        let c = completed(&overlap_example());
        assert_eq!(
            c.basis,
            vec![
                vec![(1, vec![1, 0]), (1, vec![0, 0])],
                vec![(1, vec![1, 1])],
                vec![(1, vec![0, 0, 0])],
            ]
        );
        assert_eq!(
            c.origin[0],
            vec![OriginTerm {
                coeff: 1,
                left: vec![],
                input_index: 0,
                right: vec![],
            }]
        );
        assert_eq!(
            c.origin[1],
            vec![OriginTerm {
                coeff: 1,
                left: vec![],
                input_index: 1,
                right: vec![],
            }]
        );
        // g2 = xxx arises as g1·x - y·g0 - (reduction by g0·x):
        // xxx = r0·x + y·r0 + r1·x over F_2.
        assert_eq!(
            c.origin[2],
            vec![
                OriginTerm {
                    coeff: 1,
                    left: vec![],
                    input_index: 0,
                    right: vec![0],
                },
                OriginTerm {
                    coeff: 1,
                    left: vec![1],
                    input_index: 0,
                    right: vec![],
                },
                OriginTerm {
                    coeff: 1,
                    left: vec![],
                    input_index: 1,
                    right: vec![0],
                },
            ]
        );
        let keys: Vec<_> = c
            .ambiguities
            .iter()
            .map(|e| (e.i, e.j, e.kind, e.offset))
            .collect();
        assert_eq!(
            keys,
            vec![
                (0, 2, AmbiguityKind::Overlap, 1),
                (1, 0, AmbiguityKind::Overlap, 1),
                (1, 1, AmbiguityKind::Overlap, 1),
                (2, 2, AmbiguityKind::Overlap, 1),
                (2, 2, AmbiguityKind::Overlap, 2),
            ]
        );
        // (0, 2): g0·xx - y·g2 = xxxx, one reduction by g2.
        assert_eq!(c.ambiguities[0].trace.start, vec![(1, vec![0, 0, 0, 0])]);
        assert_eq!(
            c.ambiguities[0].trace.steps,
            vec![TraceStep {
                word: vec![0, 0, 0, 0],
                basis_index: 2,
                left: vec![],
                right: vec![0],
                coeff: 1,
            }]
        );
        // (1, 0): g1·x - y·g0 = yxx. Reduce by g0·x to xxx, then by g2.
        assert_eq!(c.ambiguities[1].trace.start, vec![(1, vec![1, 0, 0])]);
        assert_eq!(
            c.ambiguities[1].trace.steps,
            vec![
                TraceStep {
                    word: vec![1, 0, 0],
                    basis_index: 0,
                    left: vec![],
                    right: vec![0],
                    coeff: 1,
                },
                TraceStep {
                    word: vec![0, 0, 0],
                    basis_index: 2,
                    left: vec![],
                    right: vec![],
                    coeff: 1,
                },
            ]
        );
        for entry in &c.ambiguities[2..] {
            assert_eq!(
                entry.trace,
                Trace {
                    start: vec![],
                    steps: vec![],
                }
            );
        }
        assert_eq!(
            c.normal_words,
            vec![
                vec![],
                vec![0],
                vec![1],
                vec![0, 0],
                vec![0, 1],
                vec![0, 0, 1],
            ]
        );
    }

    /// Hand computation for `inclusion_example` (F_2, one loop x):
    /// x⁴ + x² sits inside x⁵ as an inclusion. The overlap of x⁵ with
    /// x⁴ + x² at offset 2 gives x⁶ - x²·(x⁴ + x²) = x⁴, which reduces
    /// by x⁴ + x² to x². With x² in the basis every other composition
    /// reduces to zero. Interreduction drops x⁵ and x⁴ + x², and
    /// completion re-runs on {x²} without change.
    #[test]
    fn inclusion_collapses_to_x_squared() {
        let c = completed(&inclusion_example());
        assert_eq!(c.basis, vec![vec![(1, vec![0, 0])]]);
        assert_eq!(c.normal_words, vec![vec![], vec![0]]);
        let keys: Vec<_> = c
            .ambiguities
            .iter()
            .map(|e| (e.i, e.j, e.kind, e.offset))
            .collect();
        assert_eq!(keys, vec![(0, 0, AmbiguityKind::Overlap, 1)]);
        assert_eq!(
            c.ambiguities[0].trace,
            Trace {
                start: vec![],
                steps: vec![],
            }
        );
        assert_eq!(
            c.membership,
            vec![
                Trace {
                    start: vec![(1, vec![0, 0, 0, 0, 0])],
                    steps: vec![TraceStep {
                        word: vec![0, 0, 0, 0, 0],
                        basis_index: 0,
                        left: vec![],
                        right: vec![0, 0, 0],
                        coeff: 1,
                    }],
                },
                Trace {
                    start: vec![(1, vec![0, 0, 0, 0]), (1, vec![0, 0])],
                    steps: vec![
                        TraceStep {
                            word: vec![0, 0, 0, 0],
                            basis_index: 0,
                            left: vec![],
                            right: vec![0, 0],
                            coeff: 1,
                        },
                        TraceStep {
                            word: vec![0, 0],
                            basis_index: 0,
                            left: vec![],
                            right: vec![],
                            coeff: 1,
                        },
                    ],
                },
            ]
        );
    }

    #[test]
    fn inhomogeneous_relation_completes_without_ambiguities() {
        let c = completed(&inhomogeneous());
        assert_eq!(
            c.input_relations,
            vec![vec![(1, vec![2, 3, 4]), (4, vec![0, 1])]]
        );
        assert_eq!(c.basis, vec![vec![(1, vec![2, 3, 4]), (4, vec![0, 1])]]);
        assert!(c.ambiguities.is_empty());
        assert_eq!(
            c.membership,
            vec![Trace {
                start: vec![(1, vec![2, 3, 4]), (4, vec![0, 1])],
                steps: vec![TraceStep {
                    word: vec![2, 3, 4],
                    basis_index: 0,
                    left: vec![],
                    right: vec![],
                    coeff: 1,
                }],
            }]
        );
        // e_0..e_4, then a, c, b, d, e by (source, word), then ab, cd,
        // de. The word cde and its extensions are excluded.
        assert_eq!(
            c.normal_words,
            vec![
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![0],
                vec![2],
                vec![1],
                vec![3],
                vec![4],
                vec![0, 1],
                vec![2, 3],
                vec![3, 4],
            ]
        );
        assert_eq!(c.normal_words.len(), 13);
    }

    #[test]
    fn tight_basis_budget_truncates() {
        let limits = CompletionLimits {
            max_basis: 2,
            ..CompletionLimits::default()
        };
        assert_eq!(
            truncated(&overlap_example(), &limits),
            TruncationDiagnostics {
                basis_len: 2,
                pending_ambiguities: 2,
                steps_used: 1,
                reason: TruncationReason::BasisBudget,
            }
        );
    }

    #[test]
    fn tight_word_len_budget_truncates() {
        let limits = CompletionLimits {
            max_word_len: 3,
            ..CompletionLimits::default()
        };
        assert_eq!(
            truncated(&overlap_example(), &limits),
            TruncationDiagnostics {
                basis_len: 3,
                pending_ambiguities: 4,
                steps_used: 1,
                reason: TruncationReason::WordLenBudget,
            }
        );
    }

    #[test]
    fn tight_step_budget_truncates() {
        let limits = CompletionLimits {
            max_steps: 1,
            ..CompletionLimits::default()
        };
        assert_eq!(
            truncated(&overlap_example(), &limits),
            TruncationDiagnostics {
                basis_len: 3,
                pending_ambiguities: 4,
                steps_used: 1,
                reason: TruncationReason::StepBudget,
            }
        );
    }

    #[test]
    fn identical_input_gives_identical_bytes() {
        let p = overlap_example();
        let first = completed(&p).to_canonical_json();
        let second = completed(&p).to_canonical_json();
        assert_eq!(first, second);
    }

    #[test]
    fn input_order_does_not_change_the_basis() {
        let straight = completed(&overlap_example());
        let swapped = completed(&overlap_example_swapped());
        let a: BTreeSet<RelationData> = straight.basis.iter().cloned().collect();
        let b: BTreeSet<RelationData> = swapped.basis.iter().cloned().collect();
        assert_eq!(a, b);
    }

    #[test]
    fn free_loop_reports_empty_normal_words() {
        let c = completed(&one_loop_free());
        assert!(c.input_relations.is_empty());
        assert!(c.basis.is_empty());
        assert!(c.origin.is_empty());
        assert!(c.membership.is_empty());
        assert!(c.ambiguities.is_empty());
        // One free loop has infinitely many irreducible words. Per the
        // module contract the list stays empty and the finiteness section
        // carries the witness.
        assert_eq!(c.normal_words, Vec::<Vec<u32>>::new());
        assert_eq!(
            c.automaton,
            AutomatonData {
                states: vec![vec![]],
                transitions: vec![(0, 0, 0)],
            }
        );
        assert_eq!(
            c.finiteness,
            FinitenessData::Infinite {
                prefix: vec![],
                cycle: vec![0],
            }
        );
    }

    /// Every layer has two parallel arrows, so the path count doubles per
    /// layer and the finite language has more than 2^40 words. The work
    /// budget must stop emission before the list is materialized.
    #[test]
    fn huge_finite_language_truncates_instead_of_exhausting_memory() {
        let layers = 40u32;
        let mut arrows = Vec::new();
        for v in 0..layers {
            arrows.push((v, v + 1));
            arrows.push((v, v + 1));
        }
        let quiver = Quiver::new(layers + 1, &arrows).unwrap();
        let presentation = Presentation::new(quiver, f(2), Vec::new()).unwrap();
        let limits = CompletionLimits {
            max_steps: 10_000,
            ..CompletionLimits::default()
        };
        let started = std::time::Instant::now();
        let diagnostics = truncated(&presentation, &limits);
        assert_eq!(diagnostics.reason, TruncationReason::StepBudget);
        assert_eq!(diagnostics.steps_used, 10_000);
        assert_eq!(diagnostics.pending_ambiguities, 0);
        assert!(
            started.elapsed() < std::time::Duration::from_secs(5),
            "truncation must be fast"
        );
    }

    #[test]
    fn origins_expand_to_their_basis_elements() {
        for presentation in all_examples() {
            let c = completed(&presentation);
            let field = PrimeField::new(c.field).unwrap();
            for (j, origin) in c.origin.iter().enumerate() {
                assert_eq!(
                    expand_origin(field, &c.input_relations, origin),
                    c.basis[j],
                    "origin {j}"
                );
            }
        }
    }

    #[test]
    fn all_traces_replay_to_zero() {
        for presentation in all_examples() {
            let c = completed(&presentation);
            let field = PrimeField::new(c.field).unwrap();
            for (i, trace) in c.membership.iter().enumerate() {
                assert_eq!(trace.start, c.input_relations[i]);
                assert_trace_reduces_to_zero(field, &c.basis, trace);
            }
            for entry in &c.ambiguities {
                assert_trace_reduces_to_zero(field, &c.basis, &entry.trace);
            }
        }
    }
}
