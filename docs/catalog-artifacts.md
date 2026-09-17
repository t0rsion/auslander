# Catalog atlas artifacts

A catalog atlas artifact records a fixed-dimension module enumeration and its
self-Ext dimensions. The claim covers one checked prime field, one algebra,
one complete indecomposable catalog, and degrees zero through an inclusive
bound. Degree zero is Hom.

## Stored claim

The container schema is `auslander-computation-v1`. The kind is
`catalog-atlas-v1`, and the engine is `catalog-ext-multiplicity-v1`.
Readers reject other versions. A changed enumeration order requires a new
engine version.

The canonical JSON contains:

- The algebra completion certificate and prime modulus.
- The catalog provenance and ordered catalog identifiers.
- The target dimension vector and inclusive Ext degree bound.
- Atlas limits, multiplicity limits, and recorded work.
- Every ordered catalog-pair Ext row, including Hom.
- Multiplicity vectors and their self-Ext scores in enumeration order.
- Complete or Cut status. A Cut includes its reason, coverage, and visited
  search states.
- A fingerprint of the canonical payload.

Catalog identifiers are indices in the selected deterministic enumeration.
They are meaningful together with the certificate, provenance, and engine
version. The fingerprint detects changed bytes; it does not authenticate an
author or establish the mathematical claim.

## Replay checks

Verification parses under explicit byte and element limits. It checks declared
resource ceilings and a conservative catalog-size bound before reconstruction.
The certificate verifier checks the algebra, then replay rebuilds the catalog
through the recorded classification route.

Replay compares catalog identifiers, field, provenance, work, and Ext rows.
It recomputes each stored Ext cell with `ExtSpace::new`. It also repeats the
multiplicity search under the recorded limits and compares the entire ordered
result sequence. A valid row alone does not prove coverage. Missing rows,
duplicate rows, changed order, and modified scores fail replay.

For a Complete artifact, replay must finish the enumeration. For a Cut,
replay must reach the same cut reason, visited-state count, and exact retained
prefix. Verification does not upgrade a Cut to Complete.

The rebuilt catalog and Ext computations use library algorithms. This is
replay verification, not an independent implementation of representation
theory. Live GAP/QPA comparisons test selected algebras separately.

## Limits

Parser limits bound input bytes, arrays, integers, strings, and row counts.
Replay limits bound the algebra and catalog sizes, degree, pair and cell
counts, multiplicity search, and generic Ext checks. Declared execution
limits must fit inside the caller's replay ceilings.

Materialization checks both the number of direct-sum copies and a cell budget
for arrow matrices and relation checks. It builds block matrices without
constructing inclusion and projection witnesses.

These counters do not bound the size of every matrix inside a resolution or
the wall-clock time of a generic Ext computation. A small number of resolution
terms can still contain large modules. Resource ceilings describe their named
quantities; they are not a process-wide memory limit.

Supported catalog routes are Nakayama, zero-ideal Dynkin, and gentle-tree.
Catalog completeness justifies the fixed-dimension multiplicity search.
Stored dimensions do not encode Yoneda products, and vanishing through the
degree bound makes no claim about higher degrees.

See the [Python workflow](../crates/auslander-py/docs/catalog-workflow.md) for
construction and replay, and the [benchmark](catalog-benchmarks.md) for measured
setup, materialization, and replay costs.
