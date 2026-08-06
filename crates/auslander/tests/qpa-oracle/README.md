# QPA oracle

Differential harness comparing this library's homological output against QPA (the
GAP package "Quivers and Path Algebras"), an independent implementation with two
decades of use.

## Files

Two JSON files with the same schema, produced by independent tool chains:

- `qpa_expected.json`: committed, and the oracle. A real GAP+QPA run of
  `generate_fixtures.g` generated it. This library never writes it. The always-on
  test `library_matches_the_committed_qpa_truth` compares the library's freshly
  computed values against it, and a missing or unreadable file is a hard test
  failure, not a skip.
- `native_snapshot.json`: committed, and not an oracle. It is this library's own
  output, written by the test's `QPA_ORACLE_WRITE=1` mode. It is kept so that
  unintended drift in our values fails CI even without GAP installed. Agreement
  with it is self-consistency only. Correctness comes from `qpa_expected.json`.

`fixtures_qpa.json` is the name `generate_fixtures.g` writes into its working
directory. It is never committed here.

## Test modes (`crates/auslander/tests/qpa_oracle.rs`)

| Mode | Trigger | Behavior |
| --- | --- | --- |
| Oracle comparison | always on | library values vs `qpa_expected.json`; missing file = failure |
| Snapshot self-consistency | always on | library output vs `native_snapshot.json`, byte for byte |
| Snapshot rewrite | `QPA_ORACLE_WRITE=1` | rewrites `native_snapshot.json` only, never `qpa_expected.json` |
| Live GAP run | `QPA_ORACLE=1` | runs `generate_fixtures.g` under GAP+QPA in a temp dir, compares the fresh output against the library (values) and against `qpa_expected.json` (values, then byte for byte); fails hard when GAP is missing, QPA does not load, no output appears, or anything mismatches |

## GAP discovery (live run and regeneration)

The launcher in the test resolves GAP and QPA in this order:

1. The GAP binary is `$GAP_BIN` when set, otherwise `gap` on `PATH`. Use an
   absolute path (e.g. `/usr/bin/gap`) in shells where `gap` is aliased away.
   Spawned processes never see shell aliases, but interactive commands do.
2. GAP launches plainly when `~/.gap/pkg/qpa` exists, because GAP auto-loads
   packages from the `~/.gap` user root.
3. Otherwise `$QPA_DIR` must point at a QPA source tree. The test creates a
   temporary GAP root with `pkg/qpa` symlinked to it and launches
   `gap -q -T -l ";TMPROOT" generate_fixtures.g` (the leading `;` appends the
   root, so the standard library still resolves). QPA cannot load without its
   `gbnp` dependency in some root. When the system and user roots lack it, set
   `$GBNP_DIR` to a gbnp source tree and it is symlinked alongside.

GAP is invoked with `-q -T` and closed stdin, so an error exits nonzero instead
of hanging in a break loop. A QPA load failure is such an error.

## Regenerating `qpa_expected.json`

Only the GAP path may write this file:

```sh
cd "$(mktemp -d)"
/usr/bin/gap -q -T /path/to/crates/auslander/tests/qpa-oracle/generate_fixtures.g
cp fixtures_qpa.json /path/to/crates/auslander/tests/qpa-oracle/qpa_expected.json
```

Then run the test suite and record the new provenance (below) in this README.
`QPA_ORACLE_WRITE=1 cargo +1.92 test --test qpa_oracle` regenerates
`native_snapshot.json` after an intentional library change. It never touches
`qpa_expected.json`.

## Provenance of the committed `qpa_expected.json`

- Generated: 2026-08-05, on Arch Linux, package `gap 4.16.0-2`
  (`/usr/bin/gap`, `GAPInfo.Version` = `4.16dev`).
- QPA: version 1.36, loaded from `~/.gap/pkg/qpa`, a git clone at
  `v1.36-20-g9100462`.
- Command: `cd "$(mktemp -d)" && /usr/bin/gap -q -T
  .../tests/qpa-oracle/generate_fixtures.g && cp fixtures_qpa.json
  .../tests/qpa-oracle/qpa_expected.json` (23 fixtures written; schema v5).
- SHA-256: `b1a6222275a618623f61772b9b71d37ea139c9205a47369a338ff61c4732bf2a`.
- Two independent runs in fresh temp dirs produced byte-identical output.

## Schema v5

```json
{
  "schema": "auslander-qpa-oracle-v5",
  "convention": "right",
  "max_ext_degree": 4,
  "projdim_bound": 6,
  "injdim_bound": 6,
  "provenance": {
    "gap_version": "4.16dev",
    "qpa_version": "1.36",
    "command": "gap -q -T generate_fixtures.g"
  },
  "fixtures": [
    {
      "family": "commutative-square",
      "case": "f2",
      "field": 2,
      "presentation_id": "commutative-square",
      "ideal_id": "commutative-square",
      "order": "deglex-arrowid-v1",
      "quiver": {
        "num_vertices": 4,
        "arrows": [
          {"name": "a", "source": 0, "target": 1},
          {"name": "b", "source": 1, "target": 3},
          {"name": "c", "source": 0, "target": 2},
          {"name": "d", "source": 2, "target": 3}
        ]
      },
      "relations": [
        {"terms": [{"coeff": 1, "path": [0, 1]}, {"coeff": -1, "path": [2, 3]}]}
      ],
      "dim": 9,
      "cartan": [[1, 1, 1, 1], "..."],
      "injectives": [[1, 0, 0, 0], "..."],
      "projdim": [{"finite": 2}, "..."],
      "injdim": [{"finite": 0}, "..."],
      "tau": [{"dimvec": [1, 1, 1, 0]}, "...", {"projective": true}],
      "tau_injectives": ["..."],
      "decomposition": {
        "module": "radicals-of-projectives",
        "summands": [{"dimvec": [0, 0, 0, 1], "multiplicity": 2}, "..."]
      },
      "ext": ["..."]
    }
  ]
}
```

Identity fields:

- `family` and `case` together name the fixture and are unique across the file.
  `case` names the field, e.g. `f2` for the prime 2.
- `field`: the prime of the base field. Every fixture carries its own field;
  different fixtures use different primes.
- `presentation_id`: names the presentation content, the quiver plus the
  relations exactly as listed. Two fixtures share a `presentation_id` if and
  only if their `quiver` and `relations` values are identical. The pairs
  (`linear-an-3`, `linear-nakayama-3-2-1`) and (`a3-mod-ab`,
  `linear-nakayama-2-2-1`) share presentations; the fixtures exist separately
  because different Rust constructors build them.
- `ideal_id`: names the two-sided ideal. Two fixtures with the same `ideal_id`
  and the same `field` generate the same ideal of the same path algebra, so
  every result must agree between them even when the presentations differ.
  `commutative-square`, `redundant-presentation`, and `permuted-presentation`
  share the ideal id `commutative-square`. The concrete ideal still depends on
  the field: `characteristic-sensitive` keeps one ideal id while the ideal
  degenerates over F_2 (see below).
- `order`: the admissible order the Rust side uses, always
  `"deglex-arrowid-v1"`: longer words are larger; equal-length words compare
  lexicographically by arrow index. QPA does not consume this field; it pins
  the order the presentation data is normalized against.

Presentation fields:

- `quiver.num_vertices` and `quiver.arrows`: vertices and arrow endpoints are
  0-based (GAP is 1-based; the generator subtracts 1 on output). The position
  of an arrow in the `arrows` list is its arrow index, and it matches the
  `ArrowId` order of the Rust constructors.
- `relations`: each relation is a list of terms; each term is an integer
  `coeff` and a `path`, a list of arrow indices composed left to right. The
  consumer reduces each coefficient mod `field` and drops terms that reduce to
  zero; the surviving terms form the relation. Term order in the file is as
  written, not normalized; the sealed order sorts terms on the Rust side. This
  data reconstructs every presentation exactly.

Result fields, all computed by QPA. Vertex `i` (0-based) indexes the simple
`S_i`, the indecomposable projective `P_i`, and the indecomposable injective
`I_i`:

- `dim`: dimension of the algebra over its base field.
- `cartan`: row `i` is the dimension vector of `P_i`, computed as
  `DimensionVector` of `IndecProjectiveModules(A)` rather than via QPA's
  `CartanMatrix`, so the row meaning is pinned by construction.
- `injectives`: row `i` is the dimension vector of `I_i`, from
  `IndecInjectiveModules(A)`.
- `projdim[i]`, `injdim[i]`: the projective and injective dimensions of `S_i`,
  each either `{"finite": d}` or `{"at_least": 7}`. QPA's
  `ProjDimensionOfModule(S, 6)` and `InjDimensionOfModule(S, 6)` return `false`
  past the bound; that refusal is written as `at_least` of `projdim_bound + 1`
  (resp. `injdim_bound + 1`), exactly the payload of the `Bounded::AtLeast`
  the library returns for the same bound.
- `tau[i]`: the AR translate of `S_i`, either `{"projective": true}` when
  `S_i` is projective (the library compares `Tau::Zero`) or
  `{"dimvec": [...]}` with the dimension vector of `DTr(S_i)`.
- `tau_injectives[i]`: the same for `I_i`. The injective family supplies the
  committed non-simple tau cases across the suite.
- `decomposition`: the Krull-Schmidt decomposition of one designated test
  module per fixture. The module is the direct sum of the nonzero radicals of
  the indecomposable projectives (`module` = `"radicals-of-projectives"`).
  Each summand is reported as its dimension vector plus a multiplicity.
  Summands are sorted by dimension vector lexicographically ascending, and
  entries with equal dimension vectors are merged by adding multiplicities, so
  QPA's decomposition order never reaches the file. The comparison is on
  dimension vectors with multiplicity, not on isomorphism classes.
- `ext[i][j][k]` = `dim Ext^k(S_i, S_j)` for `k = 0..max_ext_degree`.

Schema history: v1 through v4 stored one implicit global field and untyped
values. The reader rejects every schema string except
`auslander-qpa-oracle-v5`, so a stale oracle file fails loudly instead of
silently skipping checks.

JSON is written and read by hand: the schema is small and fixed, so string
formatting plus a strict recursive-descent reader replaces a serde dependency.
Only whitespace is free-form.

## Fixture manifest

Arrow indices below are the positions in each fixture's `arrows` list. A word
like `ab` is the path `[0, 1]`: arrow 0, then arrow 1.

Carried over from v4, all over F_5, values regenerated by the live run (and
equal to the v4 values on the fields both schemas store):

| family | quiver | relations | dim |
| --- | --- | --- | --- |
| `linear-an-2` | `a1: 0->1` | none | 3 |
| `linear-an-3` | `a1: 0->1`, `a2: 1->2` | none | 6 |
| `d4-star` | `a1: 0->3`, `a2: 1->3`, `a3: 2->3` | none | 7 |
| `dual-numbers` | loop `x` | `xx` | 2 |
| `truncated-poly-3` | loop `x` | `xxx` | 3 |
| `a3-mod-ab` | `a1: 0->1`, `a2: 1->2` | `a1 a2` | 5 |
| `kronecker-2` | `a1, a2: 0->1` | none | 4 |
| `radical-square-zero-cycle-3` | cycle `a1: 0->1`, `a2: 1->2`, `a3: 2->0` | `a1 a2`, `a2 a3`, `a3 a1` | 6 |
| `linear-nakayama-3-2-1` | same presentation as `linear-an-3` | none | 6 |
| `linear-nakayama-2-2-1` | same presentation as `a3-mod-ab` | `a1 a2` | 5 |
| `cyclic-nakayama-3-3-3` | the cycle above | `a1 a2 a3`, `a2 a3 a1`, `a3 a1 a2` | 9 |
| `gentle-tree` | `a1: 0->1`, `a2: 1->2`, `a3: 1->3` | `a1 a2` | 8 |

New in v5. The square quiver is `a: 0->1` (arrow 0), `b: 1->3` (1),
`c: 0->2` (2), `d: 2->3` (3):

- `commutative-square` (`f2`, `f5`; dim 9): the square with `ab - cd`.
- `preprojective-a3` (`f2`, `f3`; dim 10): the double quiver of A3,
  arrows `a: 0->1` (0), `b: 1->2` (1), `abar: 1->0` (2), `bbar: 2->1` (3);
  relations `a abar`, `abar a - b bbar`, `bbar b`. Self-injective; every
  simple has projective and injective dimension `at_least 7`. All stored
  invariants agree between `f2` and `f3`, so this family is not the
  characteristic-sensitive witness.
- `self-overlap` (`f3`; dim 4): one vertex, loops `x` (arrow 0) and `y` (1);
  relations `xx - yy`, `xy`, `yx`. Under `deglex-arrowid-v1` the leading word
  of `xx - yy` is `yy` (equal length, `y > x`), and `yy` overlaps itself: its
  proper suffix `y` equals its proper prefix `y`, giving the self-overlap
  composition on `yyy`. Completion is also productive here: the overlap of
  `yy` with `yx` on `yyx` reduces to `xxx`, which joins the basis. The reduced
  Groebner basis is `{yy - xx, xy, yx, xxx}` with normal words
  `{e, x, y, xx}`.
- `inclusion-ambiguity` (`f2`; dim 6): the same two-loop quiver; relations
  `yx`, `xyx - xx`, `yyy`. The input leading word `xyx` properly contains the
  input leading word `yx`, an inclusion ambiguity. Completion reduces
  `xyx - xx` by `x(yx)` to `-xx`, so the reduced basis is `{xx, yx, yyy}` with
  normal words `{e, x, y, xy, yy, xyy}`.
- `inhomogeneous` (`f5`; dim 13): arrows `a: 0->1` (0), `b: 1->4` (1),
  `c: 0->2` (2), `d: 2->3` (3), `e: 3->4` (4); relation `ab - cde`, which
  mixes path lengths 2 and 3. The quiver is acyclic, so the ideal is
  admissible.
- `redundant-presentation` (`f5`; dim 9): the commutative-square ideal with a
  redundant second generator `2ab - 2cd`. On this quiver the ideal
  `(ab - cd)` is the span of `ab - cd` alone, so scalar multiples are the
  only redundant generators it admits.
- `permuted-presentation` (`f5`; dim 9): the commutative-square relation with
  its terms listed in the other order, `-cd + ab`. With one generator the
  relation list itself has no order to permute, so the term list carries the
  permutation; the sealed order normalizes both spellings to the same
  relation.
- `characteristic-sensitive` (`f2`, `f3`; dim 9): the square with
  `ab - 2cd`. Over F_3 this is `ab + cd` and the results equal
  `commutative-square`'s. Over F_2 the coefficient `-2` reduces to zero, the
  term drops, and the ideal degenerates to the monomial ideal `(ab)`.

Every result of `redundant-presentation` and `permuted-presentation` in the
committed file is equal to `commutative-square` `f5`, verified after
generation.

## Characteristic sensitivity

`characteristic-sensitive` `f2` and `f3` agree on `dim`, `cartan`,
`injectives`, `projdim`, `injdim`, and `ext`, and differ in three results:

- `tau`: `tau S_1` is `[1, 0, 1, 1]` over F_2 and `[0, 0, 1, 1]` over F_3.
- `tau_injectives`: `tau I_2` is `[1, 2, 1, 1]` over F_2 and `[0, 1, 0, 0]`
  over F_3; `I_3` is projective over F_3 but not over F_2, so one side stores
  `{"projective": true}` and the other a dimension vector `[1, 1, 1, 1]`.
- `decomposition`: over F_2 the radical of `P_0` splits as
  `[0, 1, 0, 0] + [0, 0, 1, 1]` because `ab = 0` cuts the socle; over F_3 it
  is indecomposable with dimension vector `[0, 1, 1, 1]`. The summand lists
  are `{[0,0,0,1] x2, [0,0,1,1], [0,1,0,0]}` vs `{[0,0,0,1] x2, [0,1,1,1]}`.

## Conventions

QPA works with right modules and composes paths left to right, exactly like
auslander, so the GAP output stores QPA's values verbatim under
`"convention": "right"` and the comparison is index-for-index. If a file is ever
produced under a left-module setup, mark it `"convention": "left"`. The comparator
then transposes Cartan matrices, swaps the `(i, j)` Ext indices, and reads the
`tau` rows as `τ` over the opposite algebra before comparing. Left modules over
`A` are right modules over `A^op`, every directed pairing flips, and `τ` of a
left module is `τ` over `A^op`. The archived predecessor of this library used the
left convention, which is where its `Ext^1(S_sink, S_source)` values came from.

The frozen archive repo carries vendored GAP and QPA source trees under
`external__gap/` and `external__qpa/`. They can be built for a local installation
when no system GAP is available, and `external__qpa/` is a valid `$QPA_DIR`.
