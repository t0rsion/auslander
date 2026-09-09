# Research design

The current release adds certified discovery and bounded research workflows.
It does not rename established mathematics as a new theorem. Each accelerated path
states its checked hypotheses and retains the generic calculation as a
fallback.

## Release contract

The release includes these connected parts:

- bounded-memory homological streams;
- finite-field module censuses with exact cuts;
- compiled fixed-pattern module families;
- interface-local Hom reduction where a checked separator applies;
- catalog-relative higher orthogonality over an exhaustive
  `IndecomposableCatalog`;
- incremental tilting-mutation certificates;
- portable theorem artifacts with checkpoint replay and a generic
  `ExtSpace::new` locus check;
- deterministic progress, checkpoint, resume, and report formats;
- one flagship commutative-square study and its starter census.

The public release requires all parts to share the existing conventions for
right modules, row vectors, typed partiality, and deterministic bases.

## Theorem status

The implementation distinguishes three statuses.

`Established` names a published theorem used by an algorithm. `Proved` names
an algorithm statement proved and tested in this release. `Target` names a
statement that still needs a proof and literature review. `Rejected` names a
statement that the release must not imply.

| Statement | Status | Use |
| --- | --- | --- |
| Hom of glued representations is an equalizer | Established | Checked interface Hom reduction |
| Idempotents induce recollement maps on Ext | Established | Hypothesis design for truncated Ext |
| Silting mutation follows from an approximation triangle | Established | Incremental certificate reuse |
| Rank loci in a polynomial module family are constructible | Established | Compiled rank conditions |
| Fixed outer Hom equations reduce each fiber to `ker(D_J K_J^T) K` | Proved | Fixed-interior family compiler |
| The same ranks compute `Ext^1` over a finite-dimensional path algebra | Proved | Hereditary family Ext plan |
| Directed triangular Ext fits a Mayer-Vietoris sequence under Tor vanishing | Established | Next interface Ext target |
| A two-way separator alone reduces arbitrary Ext pairs | Rejected | Generic resolutions remain available |
| General two-sided Gröbner bases update locally under mutation | Rejected | Full target recovery remains available |
| Fiberwise Krull-Schmidt multiplicities are uniform in any family | Rejected | Each specialization is checked |

The triangular target must give an explicit algorithm, connecting maps, and
cost bound. A restated equalizer or recollement sequence is not a release
claim.

## Bounded-memory homological streams

The all-at-once batch retains its module catalog and every selected
source resolution. The stream bounds the sources held by one active
batch.

The release adds a separate stream contract. The existing
`HomologicalBatch` API remains unchanged.

A self-pair stream:

1. pulls at most `max_live_sources` modules;
2. computes exact rows through `max_degree`;
3. yields rows in input order;
4. records each source `ResolutionEnd`;
5. drops the completed chunk before it pulls the next chunk;
6. ends with `Complete`, `Cut`, or `Failed`.

`max_live_sources` is a hard bound for one active batch. It is not a cache
hint. Changing it cannot change a row or its order. The bound excludes the
input census and any chunks retained by the caller.

A generic Python iterator cannot provide a durable resume point. Durable
resume requires a replayable catalog with a schema and fingerprint.

## Durable computation files

The supported long-run workflow uses a computation file with
the schema `auslander-computation-v1` and names one payload kind. The first
payload kinds are census checkpoints, census results, and homological stream
checkpoints over a portable census catalog. The separate
`auslander-theorem-v1` schema embeds a complete checkpoint and one finite
claim.

Each file stores:

- the verified algebra certificate and field;
- the request, coordinate order, and deterministic engine identifier;
- the first unfinished cursor and every exact completed counter;
- the retained witnesses needed to resume or verify the prefix;
- the cut reason or complete status;
- a fingerprint over the preceding canonical fields.

The file stores no pointer, host name, elapsed time, process id, or cache
address. A fresh process rebuilds the algebra through the certificate
verifier. It then replays the stored prefix before resume becomes available.
A fingerprint detects an accidental byte change. It is not a
signature, so replay remains the mathematical check.

The parser applies byte, integer, container, and certificate limits before
allocation. Unknown keys and schema identifiers fail. The format performs no
implicit migration.

The filesystem writer uses a temporary sibling file, flushes its contents,
and renames it over the checkpoint. A completed chunk becomes visible before
the cursor advances. A process failure can lose the live chunk, but it cannot
make the file claim that chunk completed.

Resource ceilings remain caller input on resume. The file records the limits
that produced its prefix, while the resumed request supplies new absolute
ceilings. A ceiling below committed work returns `ResumeBudget`. A ceiling
reached after more complete chunks returns a typed cut. Neither case discards
prior work.

## Certified finite census

A complete raw census fixes:

- one verified algebra over `GF(p)`;
- one dimension vector;
- arrow-id order and row-major order within each arrow matrix;
- one finite matrix search domain;
- exact candidate and classification limits.

For dimension vector `d`, the raw exponent is

```text
sum(d[source(a)] * d[target(a)] for a in arrows)
```

and the raw domain has `p` to that exponent candidates. Checked arithmetic
rejects an unrepresentable domain size.

`Module::new` decides whether a matrix tuple satisfies the relations. The
isomorphism layer classifies each valid tuple against retained
representatives. An undecided isomorphism stops the census with a typed cut.
It is never treated as non-isomorphism.

A complete result certifies the domain, final cursor, representative list,
classification counts, and canonical fingerprint. A partial result states the
next cursor and exact reason.

The raw census is exponential. Domain-specific enumerators may reduce its
work, but each reduction needs its own coverage certificate.

## Compiled module families

A compiled family fixes the algebra, dimension vector, map layout, and
parameter positions. Compilation may reuse:

- relation evaluation order;
- Hom variable offsets;
- commuting-square sparsity;
- interface restriction maps.

Compilation does not reuse an RREF or minimal resolution across parameters
without checked rank conditions. Every specialization checks the same reduced
relations as `Module::new` through a compiled arrow layout. Debug builds rerun
`Module::new`, and `specialize_generic` keeps the generic path available.

## Interface-local computation

Let the vertices split as `V1`, `S`, and `V2`. The interface `S` must separate
the two interiors. Every defining relation must lie on one side. A relation
that combines paths from both sides invalidates the basic split.

The first implementation compiles the two piece Hom spaces and solves their
compatibility over `S`. It lifts each interface kernel vector to a global
morphism and verifies the original commuting squares.

For a family whose parameters occur only on arrows inside `S`, a second plan
eliminates every other Hom equation once. If `K` is that fixed kernel and `J`
contains the interface Hom variables, each fiber solves
`ker(D_J K_J^T) K`. The final rows agree with the generic deterministic Hom
basis. The per-fiber equation matrix has no interior columns. The global lift
still writes every coordinate of each returned morphism.

Truncated Ext reduction needs additional projectivity, Tor-vanishing, or
semisimple-interface hypotheses over a nonzero relation ideal. Until a
directed triangular compiler checks those hypotheses and its connecting maps,
Ext uses the generic resolution path.

For a finite-dimensional path algebra, the standard projective resolution has
length one. Its first cochain map is the Hom constraint matrix. The
fixed-interior ranks therefore compute exact `Ext^1`, and every higher Ext
group vanishes. `InterfaceFamilyHereditaryPlan` checks the zero relation ideal
before it exposes this formula.

## Higher orthogonality

Higher orthogonality is catalog-relative. Every predicate ranges over one
exhaustive `IndecomposableCatalog`. That catalog is a Nakayama classification
or a zero-ideal Dynkin catalog. A raw census is not a catalog.

A catalog-relative d-orthogonal is not a d-cluster-tilting object. The API
does not return a global statement about the whole module category.

## Incremental mutation certificates

For `T = X + U`, mutation replaces `X` through an approximation triangle. The
Hom blocks with both endpoints in `U` do not change. Mixed blocks follow from
the triangle's long exact sequences.

The implementation may reuse those certified blocks and check the extra tilting
condition from Aihara-Iyama. It does not assume that the target presentation
updates locally. General target recovery and completion remain the fallback.

## Theorem artifacts

Discovery is not part of the trusted base. The first theorem artifact contains:

- one replay-verified complete homological checkpoint;
- a positive Ext degree interval;
- the representative indices whose self-Ext groups vanish in that interval;
- a deterministic fingerprint.

`SelfExtLocusArtifact::verify` rebuilds the census and replays every checkpoint
row. It then recomputes the locus through `ExtSpace::new`, not the homological
batch path that produced the stored rows. `ExtSpace::new` is the crate's
generic Ext constructor, not a second Ext implementation. The locus check can
stop at the first mismatch. The claim covers one finite field and one
dimension vector. It does not classify the whole module category.

## Application study

The flagship study uses the commutative square over `F_2` at dimension vector
`[2,1,1,2]`. Its complete census has 256 raw tuples, 58 accepted modules, and
12 representatives. Degree 1 vanishes at `[5,10,11]`. Degrees 1 through 3
vanish at `[5,10]`. Representative 11 has Ext dimensions `[5,0,1,0]` and is
isomorphic to `P_0 + S_0 + S_3`. A finite hand count of accepted modules is
`58 = 7^2 + 9`. The starter census at `[1,1,1,1]` keeps 16 raw tuples, 10
classes, and representative 9 as the unique vanishing class in degrees 1
through 3. Verification replays the stored rows and recomputes the locus
through `ExtSpace::new`. See
[`commutative-square-study.md`](commutative-square-study.md).

Brauer-graph, Green-hyperwalk, affine zigzag, and quaternion-algebra
computations remain motivating studies. Their observed patterns remain
examples until their scripts, proofs, and coverage records are complete.

## References

- Aihara and Iyama, *Silting mutation in triangulated categories*.
- Balmer and Favi, *Gluing techniques in triangular geometry*.
- Green and Psaroudakis, *On Artin algebras arising from Morita contexts*.
- Green, Solberg, and Zacharia, *Minimal projective resolutions*.
- Bendiffalah, *Suite exacte de Mayer-Vietoris d'une extension triangulaire*.
- Psaroudakis, *Homological theory of recollements of abelian categories*.
- Psaroudakis and Vitória, *Recollements of module categories*.
