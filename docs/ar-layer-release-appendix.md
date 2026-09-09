# Auslander-Reiten layer appendix

## QPA oracle schema v6

Freeze the schema only after a capability spike reports what GAP plus QPA can
independently produce. These constraints apply regardless of the spike result:

- Oracle fields are basis-independent invariants only: dimensions, ranks
  of named maps between named spaces, multiplicities, lexicographically
  sorted dimension-vector multisets. Never coordinates, bases, or raw
  matrices.
- The Yoneda field name is `yoneda_map_rank`, the rank of the bilinear
  multiplication map on specified `(M, N, L, m, n)`, and it enters the
  schema only if the spike shows QPA computes it independently.
- Almost-split fixtures carry start, end, and middle-term Krull-Schmidt
  identifiers (sorted dimension vectors with multiplicities), per fixture
  prime field.
- Irreducible-morphism fixtures carry `Irr` base dimensions and
  valuations on catalog domains.
- The internal duality consistency checks of section 9 stay out of the
  schema.
- `qpa_expected.json` is regenerated only by a real GAP run per the
  existing oracle policy, never from library output, and the v5 fixture
  content is preserved under the v6 envelope.

## Python surface

No `HomBasis` class is exposed.

- `Module.ext_space(other, degree) -> ExtSpace` with `dim`, `basis()`
  returning `list[ExtClass]`, `class_from_coordinates(coords)`.
- `ExtClass`: `source`, `target`, `degree`, `coordinates`,
  `representative()` (as a `Morphism`), `__add__`, `__neg__`, scalar
  `__mul__`, `__eq__` (typed error on incompatible spaces), `is_zero`,
  `then(other)`, `extension()` for degree 1.
- `ShortExactSequence`: `sub`, `middle`, `quotient`, `inclusion`,
  `projection`, `ext1_class()`, `split_status` exposing either
  (`retraction`, `section`) or the normalized inconsistency vector,
  `verify()`.
- `Module.almost_split()` returns either an `AlmostSplitSequence` or the
  enum member `AlmostSplitOutcome.PROJECTIVE`; never `None`. Decomposable
  or undetermined input raises the `ValueError` subclass
  `NotIndecomposableError`.
- `AlmostSplitSequence`: `start`, `middle`, `end`, `inclusion`,
  `projection`, `ext1_class()`, `witness_route` (string enum
  `"ar_duality"` or `"exhaustive_catalog"`), `verify()`, and a compact
  `verification_summary()` mapping check names to booleans.
- `Module.category_radical(other)`: `dim` and `basis()` of morphism
  representatives; requires both endpoints certified indecomposable and
  raises `NotIndecomposableError` otherwise.
- `Algebra.ar_quiver()`: vertices with `id`, `module`, `residue_degree`,
  `projective`, `injective`; arrows with `source`, `target`,
  `base_field_dim`, `dim_over_source_residue`, `dim_over_target_residue`,
  `representatives()`; a `plain_multiplicity` accessor that raises a
  typed error when a residue degree exceeds 1 instead of guessing.
  Unsupported domain raises `UnsupportedDomainError(ValueError)` naming
  both failed dispatch routes.
- Error taxonomy (design bullet 10): invalid endpoints, incompatible
  spaces, decomposable input, and unsupported catalog domains are
  `ValueError` subclasses; internal defect cross-check failures are
  `RuntimeError` subclasses (`DefectError`); budget exhaustion keeps the
  existing `TruncationError`, re-parented under a new
  `BudgetExhaustedError(RuntimeError)` base so future operation-specific
  budget errors share it. Re-parenting preserves every existing catch
  site because `TruncationError` remains a `RuntimeError`.
- Projective almost-split outcomes are outcomes; they never raise.

## Acceptance matrix

Two tiers:

- Ext objects, Yoneda products, extensions, and AR-duality almost-split
  sequences run on the full non-monomial matrix: the commutative
  square over F_5, preprojective A_3 over F_2, the inhomogeneous family
  over F_5, plus monomial fixtures over F_2 and F_5.
- Full AR quivers, catalog-exact rad^2, `Irr`, and `ExhaustiveCatalog`
  witnesses run where an exhaustive catalog exists: Nakayama fixtures
  (including `truncated_poly` and cyclic Nakayama) and zero-ideal Dynkin
  fixtures (A_n, D_4, orientation variants). Preprojective A_3 is
  representation-finite but has no certified catalog in this release; it
  runs tier 1 only. The docs say exactly this.

Hand-derived expected values pin at minimum: the AR sequences of
`k[x]/(x^n)` (uniserial middle terms), linear A_3 (all six vertices of
the AR quiver with its arrows), D_4 subspace orientation (the
3-arrow star), and one cyclic Nakayama algebra; Ext^1 dims and one
nonzero Yoneda square on `k[x]/(x^3)`.

## Migration and compatibility

The API keeps its existing names. The changelog states the additive surface
and the one Python MRO change (`TruncationError` under `BudgetExhaustedError`).
No migration guide is needed beyond the changelog; the README gains an
AR-layer example in both languages.

## Style

Every word this repository ships follows `docs/writing-style.md`. Names never
overclaim (`chosen_ar_class`, not `canonical_class`;
`radical_square_through_catalog` never exposed as `rad2` without its catalog;
`residue_degree`, not `residue_field`).
