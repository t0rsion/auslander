use super::automaton::PrefixAutomaton;
use super::polynomial::{
    AmbKey, KIND_OVERLAP, add_scaled, find_factor, find_reduction, lead_word, make_monic,
    origin_add_scaled, pair_ambiguities, poly_data, poly_from_relation, raw_word,
    superposition_len,
};
use super::types::{
    BasisElem, CompletionLimits, Exhausted, Origin, Outcome, Poly, TruncationDiagnostics,
    TruncationReason, Word,
};
use crate::certificate::{
    AmbiguityEntry, AmbiguityKind, CERT_SCHEMA, Certificate, FinitenessData, OriginTerm,
    QuiverData, RelationData, Trace, TraceStep,
};
use crate::field::PrimeField;
use crate::order::ORDER_ID;
use crate::order::word_cmp;
use crate::quiver::{ArrowId, Quiver};
use crate::relation::{Presentation, Relation};
use std::collections::BTreeSet;
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
    ) -> Result<(), Exhausted> {
        loop {
            let Some((term_index, basis_index, position)) = find_reduction(basis, skip, poly)
            else {
                return Ok(());
            };
            if self.steps >= self.limits.max_steps {
                return Err(Exhausted::Steps);
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
                    self.limits.max_origin_terms,
                    target,
                    neg,
                    &left,
                    &basis[basis_index].origin,
                    &right,
                )?;
            }
        }
    }

    /// All ambiguities of the ordered pair `(i, j)`, added to `out`. Errors
    /// when the key count passes `max_ambiguities`, so the set never holds
    /// more than that plus the keys of one pair.
    fn enqueue_pair(
        &self,
        basis: &[BasisElem],
        i: usize,
        j: usize,
        out: &mut BTreeSet<AmbKey>,
    ) -> Result<(), Exhausted> {
        pair_ambiguities(i, j, lead_word(&basis[i]), lead_word(&basis[j]), out);
        if out.len() > self.limits.max_ambiguities {
            return Err(Exhausted::Ambiguities);
        }
        Ok(())
    }

    /// The composition polynomial for `key`, with its provenance written
    /// into `origin` when the caller asks for it. Both kinds read
    /// `g_i·v_i - u·g_j·v_j`: overlap puts the tail on the left factor
    /// (`g_i·v - u·g_j`), inclusion on the right one (`g_i - u·g_j·v`).
    fn composition(
        &self,
        basis: &[BasisElem],
        key: AmbKey,
        origin: Option<&mut Origin>,
    ) -> Result<Poly, Exhausted> {
        let (i, j, kind, offset) = key;
        let li = lead_word(&basis[i]).clone();
        let lj = lead_word(&basis[j]).clone();
        let one = self.field.one();
        let neg_one = self.field.neg(one);
        let (u, v): (&[ArrowId], &[ArrowId]) = if kind == KIND_OVERLAP {
            (&li[..offset], &lj[li.len() - offset..])
        } else {
            (&li[..offset], &li[offset + lj.len()..])
        };
        let (vi, vj): (&[ArrowId], &[ArrowId]) = if kind == KIND_OVERLAP {
            (v, &[])
        } else {
            (&[], v)
        };
        let poly = add_scaled(self.field, &Poly::default(), one, &[], &basis[i].poly, vi);
        let poly = add_scaled(self.field, &poly, neg_one, u, &basis[j].poly, vj);
        if let Some(target) = origin {
            let max = self.limits.max_origin_terms;
            origin_add_scaled(self.field, max, target, one, &[], &basis[i].origin, vi)?;
            origin_add_scaled(self.field, max, target, neg_one, u, &basis[j].origin, vj)?;
        }
        Ok(poly)
    }

    /// Drops every element whose leading word contains another element's
    /// leading word as a factor, sorts the rest by leading word, and
    /// reduces each remaining element by the others. No surviving leading
    /// word is a factor of another, so that reduction touches only tails.
    /// Returns the reduced basis and whether it dropped any element; the
    /// caller re-runs completion while elements keep dropping.
    fn interreduce(
        &mut self,
        basis: Vec<BasisElem>,
    ) -> Result<(Vec<BasisElem>, bool), TruncationDiagnostics> {
        // Redundancy below is antisymmetric only because leading words are
        // pairwise distinct, which keeps `find_factor` strictly
        // length-decreasing between two different elements. Every word has
        // length >= 2, so a composition that reduces to a nonzero polynomial
        // has a leading word no basis element reduces, hence a new one.
        assert_eq!(
            basis.iter().map(lead_word).collect::<BTreeSet<_>>().len(),
            basis.len(),
            "leading words are pairwise distinct"
        );
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
            self.reduce_full(
                &kept,
                Some(index),
                &mut elem.poly,
                Some(&mut elem.origin),
                None,
            )
            .map_err(|error| self.diag(kept.len(), 0, error.reason()))?;
            kept[index] = elem;
        }
        Ok((kept, dropped))
    }

    fn ambiguity_keys(
        &self,
        basis: &[BasisElem],
    ) -> Result<BTreeSet<AmbKey>, TruncationDiagnostics> {
        let mut keys: BTreeSet<AmbKey> = BTreeSet::new();
        for i in 0..basis.len() {
            for j in 0..basis.len() {
                self.enqueue_pair(basis, i, j, &mut keys)
                    .map_err(|error| self.diag(basis.len(), keys.len(), error.reason()))?;
            }
        }
        Ok(keys)
    }

    fn initial_reduction(
        &mut self,
        index: usize,
        relation: &Relation,
        basis: &[BasisElem],
    ) -> Result<Option<(Poly, Origin)>, TruncationDiagnostics> {
        if relation.leading().1.len() > self.limits.max_word_len {
            return Err(self.diag(basis.len(), 0, TruncationReason::WordLenBudget));
        }
        let mut poly = poly_from_relation(relation);
        let mut origin = Origin::new();
        origin.insert((index, Vec::new(), Vec::new()), self.field.one());
        if origin.len() > self.limits.max_origin_terms {
            return Err(self.diag(basis.len(), 0, TruncationReason::OriginBudget));
        }
        self.reduce_full(basis, None, &mut poly, Some(&mut origin), None)
            .map_err(|error| self.diag(basis.len(), 0, error.reason()))?;
        if poly.is_zero() {
            return Ok(None);
        }
        Ok(Some((poly, origin)))
    }

    fn initial_basis(
        &mut self,
        presentation: &Presentation,
    ) -> Result<Vec<BasisElem>, TruncationDiagnostics> {
        let mut basis: Vec<BasisElem> = Vec::new();
        for (index, relation) in presentation.relations().iter().enumerate() {
            let Some((mut poly, mut origin)) = self.initial_reduction(index, relation, &basis)?
            else {
                continue;
            };
            if basis.len() >= self.limits.max_basis {
                return Err(self.diag(basis.len(), 0, TruncationReason::BasisBudget));
            }
            make_monic(self.field, &mut poly, &mut origin);
            basis.push(BasisElem { poly, origin });
        }
        Ok(basis)
    }

    fn reduced_composition(
        &mut self,
        basis: &[BasisElem],
        key: AmbKey,
        pending: usize,
    ) -> Result<Option<(Poly, Origin)>, TruncationDiagnostics> {
        if superposition_len(basis, key) > self.limits.max_word_len {
            return Err(self.diag(basis.len(), pending, TruncationReason::WordLenBudget));
        }
        let mut origin = Origin::new();
        let mut poly = self
            .composition(basis, key, Some(&mut origin))
            .map_err(|exhausted| self.diag(basis.len(), pending, exhausted.reason()))?;
        self.reduce_full(basis, None, &mut poly, Some(&mut origin), None)
            .map_err(|error| self.diag(basis.len(), pending, error.reason()))?;
        if poly.is_zero() {
            return Ok(None);
        }
        Ok(Some((poly, origin)))
    }

    fn enqueue_new_basis_pairs(
        &self,
        basis: &[BasisElem],
        new: usize,
        queue: &mut BTreeSet<AmbKey>,
    ) -> Result<(), TruncationDiagnostics> {
        for other in 0..basis.len() {
            self.enqueue_pair(basis, new, other, queue)
                .and_then(|()| self.enqueue_pair(basis, other, new, queue))
                .map_err(|error| self.diag(basis.len(), queue.len(), error.reason()))?;
        }
        Ok(())
    }

    fn append_composition(
        &self,
        basis: &mut Vec<BasisElem>,
        mut poly: Poly,
        mut origin: Origin,
        pending: usize,
        queue: &mut BTreeSet<AmbKey>,
    ) -> Result<(), TruncationDiagnostics> {
        if basis.len() >= self.limits.max_basis {
            return Err(self.diag(basis.len(), pending, TruncationReason::BasisBudget));
        }
        make_monic(self.field, &mut poly, &mut origin);
        basis.push(BasisElem { poly, origin });
        let new = basis.len() - 1;
        self.enqueue_new_basis_pairs(basis, new, queue)
    }

    fn process_queue(
        &mut self,
        basis: &mut Vec<BasisElem>,
        queue: &mut BTreeSet<AmbKey>,
    ) -> Result<(), TruncationDiagnostics> {
        while let Some(key) = queue.pop_first() {
            let pending = queue.len() + 1;
            if let Some((poly, origin)) = self.reduced_composition(basis, key, pending)? {
                self.append_composition(basis, poly, origin, pending, queue)?;
            }
        }
        Ok(())
    }

    fn complete_round(
        &mut self,
        mut basis: Vec<BasisElem>,
    ) -> Result<(Vec<BasisElem>, bool), TruncationDiagnostics> {
        let mut queue = self.ambiguity_keys(&basis)?;
        self.process_queue(&mut basis, &mut queue)?;
        self.interreduce(basis)
    }

    fn complete_basis(
        &mut self,
        basis: Vec<BasisElem>,
    ) -> Result<Vec<BasisElem>, TruncationDiagnostics> {
        let mut basis = basis;
        loop {
            let (reduced, dropped) = self.complete_round(basis)?;
            basis = reduced;
            if !dropped {
                return Ok(basis);
            }
        }
    }

    fn membership_traces(
        &mut self,
        presentation: &Presentation,
        basis: &[BasisElem],
        pending: usize,
    ) -> Result<Vec<Trace>, TruncationDiagnostics> {
        let mut membership = Vec::with_capacity(presentation.relations().len());
        for relation in presentation.relations() {
            let mut poly = poly_from_relation(relation);
            let start = poly_data(&poly);
            let mut steps = Vec::new();
            self.reduce_full(basis, None, &mut poly, None, Some(&mut steps))
                .map_err(|error| self.diag(basis.len(), pending, error.reason()))?;
            debug_assert!(
                poly.is_zero(),
                "input relation must reduce to zero over the final basis"
            );
            membership.push(Trace { start, steps });
        }
        Ok(membership)
    }

    fn ambiguity_entry(
        &mut self,
        basis: &[BasisElem],
        key: AmbKey,
        pending: usize,
    ) -> Result<AmbiguityEntry, TruncationDiagnostics> {
        // No provenance is emitted for compositions, so this reduction skips
        // the origin budget.
        let mut poly = self
            .composition(basis, key, None)
            .map_err(|exhausted| self.diag(basis.len(), pending, exhausted.reason()))?;
        let start = poly_data(&poly);
        let mut steps = Vec::new();
        self.reduce_full(basis, None, &mut poly, None, Some(&mut steps))
            .map_err(|error| self.diag(basis.len(), pending, error.reason()))?;
        debug_assert!(
            poly.is_zero(),
            "composition must reduce to zero over the final basis"
        );
        let (i, j, kind, offset) = key;
        Ok(AmbiguityEntry {
            i,
            j,
            kind: if kind == KIND_OVERLAP {
                AmbiguityKind::Overlap
            } else {
                AmbiguityKind::Inclusion
            },
            offset,
            trace: Trace { start, steps },
        })
    }

    fn ambiguity_traces(
        &mut self,
        basis: &[BasisElem],
        keys: &BTreeSet<AmbKey>,
    ) -> Result<Vec<AmbiguityEntry>, TruncationDiagnostics> {
        let total = keys.len();
        let mut ambiguities = Vec::with_capacity(total);
        for (done, &key) in keys.iter().enumerate() {
            ambiguities.push(self.ambiguity_entry(basis, key, total - done)?);
        }
        Ok(ambiguities)
    }

    fn finiteness_data(
        &mut self,
        quiver: &Quiver,
        leads: &[&Word],
        basis_len: usize,
    ) -> Result<(PrefixAutomaton, FinitenessData, Vec<Vec<u32>>), TruncationDiagnostics> {
        let automaton = PrefixAutomaton::build(quiver, leads);
        let (finiteness, normal_words) = match automaton.cycle_witness() {
            Some((prefix, cycle)) => (FinitenessData::Infinite { prefix, cycle }, Vec::new()),
            None => (
                FinitenessData::Finite,
                self.normal_words(quiver, &automaton, basis_len)?,
            ),
        };
        Ok((automaton, finiteness, normal_words))
    }

    fn emit(
        &mut self,
        presentation: &Presentation,
        basis: &[BasisElem],
    ) -> Result<Certificate, TruncationDiagnostics> {
        let keys = self.ambiguity_keys(basis)?;
        let input_relations: Vec<RelationData> = presentation
            .relations()
            .iter()
            .map(|r| poly_data(&poly_from_relation(r)))
            .collect();
        let membership = self.membership_traces(presentation, basis, keys.len())?;
        let ambiguities = self.ambiguity_traces(basis, &keys)?;
        let leads: Vec<&Word> = basis.iter().map(lead_word).collect();
        let quiver = presentation.quiver();
        let (automaton, finiteness, normal_words) =
            self.finiteness_data(quiver, &leads, basis.len())?;
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

    /// Every normal word of the final basis, in the fixed basis order.
    /// Each emitted word costs one work unit, checked before the word is
    /// allocated.
    fn normal_words(
        &mut self,
        quiver: &Quiver,
        automaton: &PrefixAutomaton,
        basis_len: usize,
    ) -> Result<Vec<Vec<u32>>, TruncationDiagnostics> {
        let mut rows: Vec<(u32, u32, Word, usize)> = Vec::new();
        for v in 0..quiver.num_vertices() {
            if self.steps >= self.limits.max_steps {
                return Err(self.diag(basis_len, 0, TruncationReason::StepBudget));
            }
            self.steps += 1;
            rows.push((v, v, Vec::new(), v as usize));
        }
        let mut level_start = 0;
        while level_start < rows.len() {
            let level_end = rows.len();
            for i in level_start..level_end {
                let (source, target, word, state) = rows[i].clone();
                for &a in quiver.arrows_from(target) {
                    if let Some(next) = automaton.step(state, a) {
                        if self.steps >= self.limits.max_steps {
                            return Err(self.diag(basis_len, 0, TruncationReason::StepBudget));
                        }
                        self.steps += 1;
                        let mut extended = word.clone();
                        extended.push(a);
                        rows.push((source, quiver.target(a), extended, next));
                    }
                }
            }
            level_start = level_end;
        }
        rows.sort_by(|(sa, _, wa, _), (sb, _, wb, _)| {
            wa.len().cmp(&wb.len()).then(sa.cmp(sb)).then(wa.cmp(wb))
        });
        Ok(rows
            .into_iter()
            .map(|(_, _, word, _)| raw_word(&word))
            .collect())
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
/// ideal and emits a certificate, or reports truncation when a budget of
/// `limits` runs out. See the module documentation for the composition
/// formulas, the processing order, and the `normal_words` contract.
pub(super) fn complete(presentation: &Presentation, limits: &CompletionLimits) -> Outcome {
    run(presentation, limits).map_or_else(Outcome::Truncated, Outcome::Complete)
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
    let basis = engine.initial_basis(presentation)?;
    let basis = engine.complete_basis(basis)?;
    engine.emit(presentation, &basis)
}
