# Certified derived classification

This document fixes the v0.10 derived-classification contract. A deviation
needs a documented reason and a design update in the same change.

`classify_derived` partitions a finite family of algebras over one prime
field. Every merge carries a replayable derived-equivalence witness. Every
separated pair of classes carries a derived invariant with different values.
A pair that neither side settles is typed `Unresolved`.

The v0.7 workbench proves equivalence and never proves inequivalence.
`discover_equivalences` returns `IncompleteEquivalenceGraph`. Only the stop
`ExhaustedFrontier` carries a closure claim: the stored vertices are closed
under left and right mutation up to isomorphism. Without an `Undetermined`
blocker, they are every tilting complex reachable from the regular complex
through a chain of tilting mutations. With `DiscoveryLimits::through_silting`,
they are every silting complex reachable through a chain of irreducible
silting mutations. Neither claim covers other silting complexes or the whole
derived equivalence class, so it never separates two algebras. This release
adds the negative side and the driver that combines both sides.

## 1. Scope

In scope:

- Checked derived invariants of one verified algebra: vertex count, integer
  Cartan invariants, bounded Hochschild cohomology dimensions, and two
  invariants of a gentle presentation: the Avella-Alaminos-Geiss function
  and the winding class.
- `DerivedInequivalenceWitness`: two algebras and one invariant whose values
  differ. The verifier recomputes both values.
- Recognition of gentle presentations with cycles, loops, and multiple
  arrows. Gentle-tree catalogs keep their v0.9 domain.
- Enumeration of connected gentle presentations with `n` vertices, one per
  isomorphism class of bound quiver.
- An algebra isomorphism witness from a recovered target presentation to a
  family member.
- `classify_derived(family, limits, control)` and the portable
  `derived-atlas-v1` artifact with a standalone replay verifier.
- One flagship study: every connected gentle algebra with at most `N`
  vertices over `F_2`. The measured reach of discovery fixes `N`.
- A dependency-free WebAssembly build of the artifact verifiers and one
  static page that replays an artifact in the browser.

Outside this scope: non-split targets, extension fields, characteristic
zero, and a decision procedure for integral congruence of Cartan matrices.

## 2. Invariants

Each invariant is established mathematics. The implementation computes it
exactly or returns a typed cut. Two algebras are separated only by values
that both finished.

| Invariant | Value | Condition | Source |
| --- | --- | --- | --- |
| Vertex count | `n` | none | rank of `K_0` |
| Cartan determinant | `det C` in `Z` | none | Euler form |
| Invariant factors | of `C`, `C + C^T`, `C - C^T` | none | Euler form |
| Cartan pencil | `det(xC + C^T)` in `Z[x]` | none | Euler form |
| AAG function | multiset of pairs `(n, m)` | both presentations gentle | Avella-Alaminos, Geiss |
| Winding class | planar, gcd, parity, or Arf value | both presentations gentle | Lekili, Polishchuk; Amiot, Plamondon, Schroll |
| Hochschild dimensions | `dim HH^i` for `i <= d` | bar limits | Rickard, Happel |
| Center dimension | `dim HH^0` | bar limits | Rickard |

The rows run cheap first. The two gentle rows need recognition and one walk
over the ribbon graph, so they precede the bar computation.

The AAG function and the winding class together form a complete derived
invariant of a connected gentle algebra (Amiot, Plamondon, Schroll, Theorem
5.4). In genus 0 the winding class is `planar` and adds nothing. Some
statements of the invariance assume an algebraically closed field. A derived
equivalence over `GF(p)` extends to the algebraic closure, so a difference in
either value separates over `GF(p)` too. The construction and its checks are in
[`gentle-derived-invariant.md`](gentle-derived-invariant.md). The library never
merges on equal invariants: a merge always needs a tilting witness.

The Euler form rows use one fact. A derived equivalence `D(A) -> D(B)`
restricts to perfect complexes and induces an isometry of `K_0(per A)` and
`K_0(per B)` for the form `sum (-1)^i dim Hom(X, Y[i])`. On the basis of
indecomposable projectives the Gram matrix is the Cartan matrix. Hence
`C_B = X C_A X^T` for some `X` in `GL_n(Z)`. Every row of the table above
labeled "Euler form" is invariant under that congruence. The pencil
`det(xC + C^T)` needs no finite global dimension: `det(X)^2 = 1`. When
`det C` is nonzero, the pencil divided by `det C` is the Coxeter polynomial.

Hochschild cohomology dimensions depend on the field. Both algebras of a
witness live over the same `GF(p)`.

The Avella-Alaminos-Geiss function applies only when both presentations are
recognized as gentle. A presentation that fails recognition proves nothing
about the algebra, so recognition failure never separates two algebras. Its
reading is `NotApplicable` with the recognition error. That reading is not a
stop: larger limits give the same reading.

The gentle surface model gives one checked consistency identity. With `M`
permitted threads and `b` pairs in the AAG function, the genus is
`g = (n - M - b + 2) / 2`. A negative or fractional value is an
implementation defect, and tests assert that it never occurs.

## 3. Witnesses

`DerivedInequivalenceWitness` stores two algebra certificates, the
invariant, and the two differing values. `verify()` rebuilds both algebras
through the certificate verifier and recomputes the named invariant for each.
It accepts only when both recomputed values finish and differ.

A merge joins a walked member and a matched member. It stores the mutation
recipe from the regular complex of the walked member, the
`DerivedEquivalencePath` from the walked member to the recovered target, and
an `AlgebraIsomorphism` from that target to the matched member. The merges
of a class form a spanning tree of its members.

Deviation: the path starts at the walked member, not at the class
representative. A path continues only from an identical certificate, and a
recovered target is only isomorphic to a member. Composing through the
isomorphism would need transport of tilting complexes along it, which this
release does not implement. A spanning tree of merges proves the class
because derived equivalence is transitive.

The isomorphism stores a vertex bijection and one normal-word coordinate
vector per arrow. Its verifier checks five facts: the vertex map is a
bijection, each arrow image lies in the radical corner of its endpoints,
every relation maps to zero, the arrow images span the arrow space modulo
`rad^2`, and dimensions agree. The first two define an algebra map from the
path algebra. The other three make the induced map an isomorphism.

## 4. Classification

`classify_derived` runs in three stages.

1. Compute the invariants of every member under caller limits.
2. Separate members whose finished invariants differ. Store one witness per
   separated pair of classes: the first differing invariant in table order,
   the least over every member pair of the two classes.
3. Inside each group, walk mutations from each member whose class still has
   an unresolved partner in the group. Recover the target of each tilting
   vertex, match it against the whole family, and merge on a verified
   isomorphism.

A group is a connected component of the member pairs that no finished
invariant separates. A stopped reading makes non-separation intransitive, so
equal values do not define a partition. When every reading finishes, the
groups are the classes of equal values, and a class has an unresolved partner
exactly when its group is not yet one class.

A match whose classes are separated is an internal defect, typed
`ClassificationError::Contradiction`. A match in another group cannot
occur, because members of different groups are separated.

Members with equal gentle keys, or equal certificates when not gentle, are
duplicates. Each merges into the first such member with an empty recipe and
the identity path, and it is never walked.

The result stores the classes, the separations, and every unresolved pair
with the walks that could have merged it: every walk from a member of either
class. Each walk records its discovery stop. `DerivedClassification::status()`
is `Complete` exactly when no pair is unresolved. A resource limit or a
cancellation never turns an unresolved pair into a separation or a merge.

### Walks through silting complexes

`ClassificationLimits::discovery` fixes the walk. With `through_silting` set,
a walk stores a silting complex that is not tilting as a vertex and mutates
it further. Such a vertex counts toward `max_vertices`, has no target, and
never gives a merge. A merge recipe can then pass through silting steps. Its
last complex carries a full tilting certificate, and Rickard's theorem needs
nothing more. The certificate proves generation through the chain of cone
relations back to the regular complex. Each link needs only that its parent
generates, so a silting parent suffices. Irreducible mutation of a silting
complex is silting (Aihara and Iyama, Theorem 2.31), so a silting walk has no
`SiltingOnly` blocker.

A tilting walk can miss a derived equivalence that a silting walk finds. The
tilting walks from members 470 and 724 of `connected_gentle_algebras(4, F_2)`
leave the pair open: each recovers only targets of its own class. A silting
walk from 470 reaches a tilting complex whose target is 724. The test
`a_walk_through_silting_complexes_merges_an_open_pair` pins this pair.

## 5. Portable artifact

`derived-atlas-v1` is a payload kind under `auslander-computation-v1` with
engine `derived-classification-v1`. `DerivedClassification::to_artifact`
writes it. `verify_derived_atlas_artifact(text, limits, control)` replays
it and returns the rebuilt `DerivedClassification`. `auslander verify` and
the [browser verifier](browser-verifier.md) select it through the artifact
dispatch.

The keys appear in this order. Unknown or reordered keys fail, and so does
any text that does not serialize back to the same bytes.

| Key | Content |
| --- | --- |
| `schema`, `kind`, `engine` | the three identifiers |
| `field` | the prime `p` |
| `limits` | `invariants` (Hochschild degree, bar limits), `discovery` (walk limits, `max_hom_spaces`, `through_silting`), `target` (target and completion limits) |
| `members` | one certificate per member, an escaped JSON string as in `catalog-atlas-v1` |
| `invariants` | per member, one row per kind in table order: `kind`, `reading`, then `value` or `stop` |
| `classes` | `members`, then `merges`: `source`, `member`, `recipe`, `vertex_map`, `arrow_images` |
| `separations` | `classes`, `members`, `kind`, `left`, `right` |
| `unresolved` | `classes`, and `walks` as indices into `walks` |
| `walks` | `member`, `stop`, and six counters, from `vertices` to `merges` |
| `status` | `complete` or `incomplete` |
| `fingerprint` | FNV-1a of the preceding canonical bytes |

A finished value is a list of integers. A count or a determinant is one
entry. Invariant factors, pencil coefficients, and Hochschild dimensions are
listed in order. An AAG function is `n_1, m_1, n_2, m_2, ...`. A winding
class is `[0]` planar, `[1, g]` gcd, `[2]` odd, `[3]` even, or `[4, a]`
Arf. A stop is `overflow` or `bar_cut`. A recipe step is
`[direction, summand]`, as in `auslander-derived-v2`. An arrow image lists
residues in `0..p` over the normal-word basis of the matched member.

The verifier runs the cheap checks first:

1. The fingerprint matches, and every declared limit lies within its
   ceiling in `DerivedAtlasVerifyLimits`. A limit above its ceiling stops
   with `ArtifactVerificationCut::DeclaredLimit`. So does a member
   certificate with more than `max_member_dimension` vertices or normal
   words, before any member is built.
2. The classes partition the family. No merge joins the classes of an
   unresolved pair, and no separation names them. The merges of each class
   form a spanning tree. Each pair of classes is separated or unresolved
   exactly once. The walks run in member order, each walk adds exactly the
   merges with a recipe from its member, and each unresolved pair lists
   every walk from a member of either class. The status is `complete`
   exactly when no pair is unresolved.
3. Every member rebuilds through the certificate verifier, and every
   reading recomputes to its stored form.
4. Every separation rebuilds a `DerivedInequivalenceWitness` from the
   recomputed readings of its two members, with the stored values.
5. Every recipe replays through `replay_recipe`, the recovered target maps
   onto the member, and the `AlgebraIsomorphism` verifies. An empty recipe
   is a duplicate, and its target is the source member. Without
   `through_silting`, a step that gives a silting complex that is not
   tilting fails, because a tilting walk never stores one.

It runs no discovery. Cancellation is checked before each member and each
merge and stops with `Cancelled`. `replay.max_work_units` bounds the
mutations replayed over all merges and stops with `WorkLimit`. Both count
the mutations replayed so far.

Limits of the format:

- A walk record is a claim about discovery. The verifier checks its member
  and its merges but does not rerun the walk. A stored stop, such as
  `exhausted_frontier`, and the other counters are not checked. The stops of
  the listed walks are the typed reasons of an unresolved pair.
- A stop or `not_applicable` reading stores no diagnostics or recognition
  error. The recomputed reading must have the same variant.
- A cancelled reading has no stored form, because no replay reproduces it.
  `to_artifact` returns `DerivedAtlasError::CancelledReading` for it.

`crates/auslander/artifacts/research/derived-atlas-f2-n3.json` classifies
the 88 connected gentle algebras with at most 3 vertices over `F_2` as one
family: 40 classes and no unresolved pair, in 229608 bytes.
`derived-atlas-f2-n4.json` classifies the 982 with at most 4 vertices, with
silting walks of 64 vertices: 143 classes and one unresolved pair, in
3299973 bytes.

### Command line

`auslander classify gentle` runs the flagship study. It classifies each
family `connected_gentle_algebras(n, field)` for `n` from 1 to `N` and
prints one table row per family. It exits with status 1 when a
classification fails or does not verify. `auslander classify gentle --help`
lists the options.

- `--walk-vertices W` sets `ClassificationLimits::with_walk_vertices(W)`,
  default 8. `--hochschild-degree D` sets `invariants.hochschild_degree`.
  `--through-silting` sets `discovery.through_silting`.
- `--record FILE` writes the `derived-classification-study-v1` record: the
  limits, and per family the counts and the wall times of each stage.
- `--output FILE` classifies every member with at most `N` vertices again,
  as one family. It verifies the atlas, then writes it.

These commands write the committed records:

```sh
cargo build --release -p auslander --bin auslander
target/release/auslander classify gentle --vertices 3 --field 2 \
  --record derived-classification-f2-n3.json --output derived-atlas-f2-n3.json
target/release/auslander classify gentle --vertices 4 --field 2 \
  --walk-vertices 64 --through-silting \
  --record derived-classification-f2-n4.json --output derived-atlas-f2-n4.json
```

The atlas is byte-identical on every run. The record differs in its wall
times.

`auslander inspect FILE` parses an atlas without replay. `auslander verify
FILE` replays it. Both print the counts, the status, the walk count, and the
first 10 classes and unresolved pairs, each list followed by the number it
leaves out. A pair line ends with the stops of its walks, labeled
`recorded stops (not replayed)`, because neither command reruns a walk.

## 6. Gates

- Every certified mutation edge in the test corpus joins algebras with equal
  invariants. A difference is a defect.
- `A_n` path algebras have the AAG function `[(n + 1, n - 1)]`.
- The genus identity holds for every enumerated gentle presentation.
- Tampered witnesses, isomorphisms, and artifacts fail verification. The
  seeded mutation test in `crates/auslander-wasm/tests/mutation.rs` edits
  every committed artifact and parity fixture, reseals the fingerprint, and
  checks that no mutant panics or verifies a changed claim. Its ignored
  variant runs the committed atlas too.
- Fresh-process determinism for classifications and artifacts.
- `F_2` and `F_3` fixtures, Python parity, and the WebAssembly verifier
  agree with the native verifier on the same artifact bytes.

## References

- T. Aihara and O. Iyama, *Silting mutation in triangulated categories*,
  J. London Math. Soc. (2) 85 (2012), 633-668. arXiv:1009.3370.
- C. Amiot, P.-G. Plamondon, and S. Schroll, *A complete derived invariant
  for gentle algebras via winding numbers and Arf invariants*, Selecta Math.
  (N.S.) 29 (2023), paper 30. arXiv:1904.02555.
- D. Avella-Alaminos and C. Geiss, *Combinatorial derived invariants for
  gentle algebras*, J. Pure Appl. Algebra 212 (2008), 228-243.
- D. Happel, *Hochschild cohomology of finite-dimensional algebras*, in
  Séminaire d'Algèbre Paul Dubreil et Marie-Paul Malliavin, Lecture Notes in
  Math. 1404, Springer, 1989, 108-126.
- Y. Lekili and A. Polishchuk, *Derived equivalences of gentle algebras via
  Fukaya categories*, Math. Ann. 376 (2020), 187-225. arXiv:1801.06370.
- J. Rickard, *Morita theory for derived categories*, J. London Math. Soc.
  (2) 39 (1989), 436-456.
- J. Rickard, *Derived equivalences as derived functors*, J. London Math.
  Soc. (2) 43 (1991), 37-48.

Theorem numbers refer to the arXiv versions: arXiv:1009.3370v3 for Aihara
and Iyama, and the versions that
[`gentle-derived-invariant.md`](gentle-derived-invariant.md) lists for the
gentle papers.
