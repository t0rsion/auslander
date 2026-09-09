//! The budgeted mutation walk from `(A, 0)` and its closure certificate.
//!
//! [`support_tau_tilting_graph`] walks the support tau-tilting quiver breadth
//! first from the pair `(A, 0)`, closing under left mutation alone. When the
//! frontier empties, the walk builds a [`ClosureWitness`] and reruns
//! [`ClosureWitness::verify`] on it before the outcome exists. Only a witness
//! that passes becomes [`SupportTauTiltingGraphOutcome::Closed`], whose vertex
//! list is every basic support tau-tilting pair of the algebra, up to
//! isomorphism. A drained frontier alone is not the certificate: it says the
//! builder found a branch at every slot, not that the seven obligations hold.
//! When a budget runs out or a certification is blocked, the outcome is
//! [`SupportTauTiltingGraphOutcome::Incomplete`], which keeps the partial
//! graph and makes no completeness claim. When the recheck itself fails, the
//! result is [`GraphError::Defect`] and no graph comes back at all.
//!
//! # The certificate
//!
//! What the obligations establish is finite left closure. Let `S` be a finite
//! set of basic support tau-tilting pairs with `(A, 0)` in `S`, such that
//! every left mutation of every member of `S` is again in `S`. Then `S` is
//! every basic support tau-tilting pair.
//!
//! The proof takes two facts from Adachi, Iyama, and Reiten, "tau-tilting
//! theory", Compositio Math. 150 (2014), 415-452. `(A, 0)` is the maximum of
//! the partial order on support tau-tilting modules (AIR, section 2, the
//! sentence introducing the order). Theorem 2.35(b) says that for `U < V`
//! there is a left mutation `V'` of `V` with `V' >= U`. Take any support
//! tau-tilting pair `U`. If `U` is `(A, 0)` it is in `S`. Otherwise
//! `(A, 0) > U`, so Theorem 2.35(b) gives a left mutation `V_1` of `(A, 0)`
//! with `V_1 >= U`, and `V_1` is in `S` by left closure. Iterating gives a
//! strictly decreasing chain `(A, 0) > V_1 > V_2 > ...` inside `S` with every
//! `V_i >= U`. `S` is finite, so the chain stops, and it can only stop at `U`.
//! Hence `U` is in `S`.
//!
//! The citation is AIR Theorem 2.35(b), equivalently the descending half of
//! the proof of AIR Corollary 2.38. It is not Theorem 2.18 applied to a finite
//! component, and it is not Corollary 2.38 itself. Corollary 2.38 reads "a
//! finite connected component of the support tau-tilting quiver is the whole
//! quiver", and appealing to it directly would also have to rule out mutations
//! from outside `S` landing inside it, which the walk never checks. The
//! argument above needs neither connectivity nor `n`-regularity, only the
//! maximum, left closure, and finiteness.
//!
//! For a finite-dimensional admissible bound quiver algebra over a checked
//! prime field, a verified finite set containing `(A, 0)` and closed under
//! every left mutation is the complete set of basic support tau-tilting pairs
//! up to isomorphism, by AIR Theorem 2.18 and Theorem 2.35(b). It requires
//! neither an algebraically closed base field nor residue division rings
//! equal to the base field.
//!
//! The field-generality clause rests on the AIR hypothesis itself, which
//! reads "let `Lambda` be a finite dimensional `k`-algebra". The paper
//! re-imposes the algebraically closed hypothesis at the head of section 5,
//! which would be pointless if it were already in force. Demonet, Iyama, and
//! Jasso, "tau-tilting finite algebras, bricks and g-vectors"
//! (arXiv:1503.00285), work over an arbitrary field with right modules, this
//! crate's setting, and restate the results the argument uses. Cite AIR
//! Theorem 2.35(b) by number and by statement: the published numbering may
//! differ from the arXiv v4 numbering the citation was checked against.
//!
//! Mutation at a summand of the projective part is always a right mutation,
//! so a descending walk never performs one and a slot is an index into the
//! module summands. `n`-regularity of the quiver is a cross-check here, not a
//! step of the proof.
//!
//! # What closure means in code
//!
//! Closure is checked per vertex and per slot, never inferred. A set closed
//! under a subset of the left mutations proves nothing, so
//! [`ClosureWitness::verify`] requires that every module-summand slot of every
//! vertex carries one of two things: a verified left mutation whose target is
//! a vertex of the set, or a certified [`crate::mutation::FacWitness`] proving that the slot
//! admits no left mutation.
//!
//! That recheck is a gate, not an optional call. It runs on every drained
//! walk before the closed value is built, so a construction defect surfaces
//! as [`GraphError::Defect`] rather than as a
//! [`ClosedSupportTauTiltingGraph`] whose own `verify` returns false. On D_4
//! it costs 74.4 ms to 124.2 ms against 18.7 ms to 30.9 ms for the walk, over
//! four dev-profile runs per field. The cost is not charged to
//! `max_work_units`, which budgets the walk.
//!
//! # Truncation is structurally biased
//!
//! An [`IncompleteSupportTauTiltingGraph`] is a biased sample, not a nearly
//! complete list. On a tau-tilting infinite algebra the descending walk runs
//! down one ray forever. Over the Kronecker algebra it descends the
//! preprojective ray, `(m, m + 1) + (m + 1, m + 2)`, and never reaches a
//! single preinjective vertex, because no finite chain of Hasse steps down
//! from `(A, 0)` leaves that ray. Do not read a truncated result as "the pairs
//! found so far, of which there may be a few more".
//!
//! A truncated set is never accidentally closed. At the moment of truncation
//! the deepest vertex still has an unvisited slot, so the closure test fails.
//! No false completeness certificate is possible. The only risk is never
//! getting one.
//!
//! # Cost and budgets
//!
//! One [`crate::taurigid::TauCache`] is shared across the whole walk, keyed by nominal module
//! identity, one entry per discovered indecomposable summand. `tau` never
//! runs on an assembled module, which follows from additivity of `tau` and
//! `Hom` and so is not a heuristic. Identity keying is what makes the cache
//! sound: a dimension vector is an isomorphism invariant and no identifier,
//! so an earlier index-keyed cache returned the translate of one module for
//! another that merely shared its dimensions. A freshly rebuilt but
//! isomorphic module misses, which costs time and never correctness.
//! Preserving known decompositions is what keeps those misses rare.
//!
//! The limit of that sharing is the price of the identity key. Every
//! decomposition returns fresh module values, so a module rebuilt from an
//! isomorphic one misses even though the class is already known. On D_4 the
//! walk computes 200 translates and answers 450 further calls from the cache,
//! against 12 isomorphism classes. Recovering those hits needs reuse across
//! separately reconstructed but isomorphic summands, which is deferred: it
//! must not reintroduce a key weaker than identity.
//!
//! [`MutationGraphLimits`] carries four budgets and no wall-clock limit. Work
//! units are charged by call and by module size, never by time, so the count is
//! the same in every profile and on every platform. `max_work_units` is the
//! only budget that covers the whole walk. `max_matrix_entries` gates one Hom
//! system per slot, the one the `Fac` test builds, and nothing else. See
//! [`MutationGraphLimits::max_matrix_entries`] for what falls outside it.
//!
//! The size half of that rate is what makes `max_work_units` brake a
//! tau-tilting infinite walk. Charged by call alone, a Kronecker walk charged
//! units that grew far more slowly than its cost, so a ceiling well below the
//! default never fired. The modules on the preprojective ray grow without
//! bound, and every Hom system on them was charged one unit. With the size
//! factor the same walk stops well short of its vertex ceiling on the default
//! 50 million work units, which is the point of the rate. See
//! [`ClosedSupportTauTiltingGraph::work_units`] for the rates.

mod contracts;
mod support;
mod verify;
mod walk;

pub use contracts::*;
pub use verify::ClosureWitness;
pub use walk::support_tau_tilting_graph;

#[cfg(test)]
mod tests;
