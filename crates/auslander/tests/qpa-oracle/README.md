# QPA oracle

Differential harness comparing this library's homological output against QPA (the
GAP package "Quivers and Path Algebras"), an independent implementation with two
decades of use.

## Files

Two JSON files, produced by independent tool chains, both at schema v6:

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

The harness computes every v6 field from the library and compares it entry by
entry. Designated modules are built by construction from their kind and index,
never looked up by dimension vector. Almost-split sequences come from
`almost_split`, and the `ArDualityWitness` of every sequence the harness builds
is rechecked before its values are used. The irreducible morphisms out of a
module are computed over the opposite algebra on its dual, which is the same
computation as the morphisms into a module: `opposite` keeps the vertex ids and
`dual` keeps the dimension vector, so the values compare directly.

The always-on modes take about a minute. The workspace sets `opt-level = 2` for
the dev profile, because at `opt-level = 0` this suite takes over ten minutes
locally and stalls the Windows CI runner. Debug assertions and overflow checks
stay on. `inclusion-ambiguity` dominates: its almost-split sequences run on
modules of dimension 18 and 24 over a 6-dimensional algebra, and every value is
computed twice, once over the algebra and once over its opposite for the
left-convention test.

## GAP discovery (live run and regeneration)

The launcher in the test resolves GAP and QPA in this order:

1. The GAP binary is `$GAP_BIN` when set, otherwise `gap` on `PATH`. Use an
   absolute path (e.g. `/usr/bin/gap`) in shells where `gap` is aliased away.
   Spawned processes never see shell aliases, but interactive commands do.
2. GAP launches plainly when `~/.gap/pkg/qpa` exists, because GAP auto-loads
   packages from the `~/.gap` user root.
3. Otherwise `$QPA_DIR` must point at a QPA source tree. The test creates a
   temporary GAP root with `pkg/qpa` symlinked to it and launches
   `gap -q -T -m 1g -l ";TMPROOT" generate_fixtures.g` (the leading `;` appends
   the root, so the standard library still resolves). QPA cannot load without
   its `gbnp` dependency in some root. When the system and user roots lack it,
   set `$GBNP_DIR` to a gbnp source tree and it is symlinked alongside.

GAP is invoked with `-q -T` and closed stdin, so an error exits nonzero instead
of hanging in a break loop. A QPA load failure is such an error. `-m 1g` asks
for a large initial workspace, which the v6 workload needs (see below).

## Regenerating the oracle

Only the GAP path may write these files:

```sh
cd "$(mktemp -d)"
/usr/bin/gap -q -T -m 1g \
   /path/to/crates/auslander/tests/qpa-oracle/generate_fixtures.g
cp fixtures_qpa.json \
   /path/to/crates/auslander/tests/qpa-oracle/qpa_expected.json
```

The generator emits schema v6.

GAP 4.16dev crashes on this workload, with a segmentation fault and no message.
It crashed on two of five runs of the command above and on none of three runs of
the same command with `-m 1g`, which asks for a large initial workspace. The
flag changes nothing in the output: every completed run, with the flag and
without, wrote the same bytes. Raising the shell stack limit does not help; with
`ulimit -s unlimited` GAP crashed sooner. Use `-m 1g` and expect a run to take
about 75 s. A crashed run leaves no `fixtures_qpa.json`, so a crash cannot
produce a truncated file. Repeat the run until it completes, then confirm two
completed runs in fresh directories agree byte for byte before copying either
one.

Then run the test suite and record the new provenance (below) in this README.
`QPA_ORACLE_WRITE=1 cargo +1.92 test --test qpa_oracle` regenerates
`native_snapshot.json` after an intentional library change. It never touches
`qpa_expected.json`.

## Provenance of the committed `qpa_expected.json`

- Generated: 2026-08-06, on Arch Linux, package `gap 4.16.0-2`
  (`/usr/bin/gap`, `GAPInfo.Version` = `4.16dev`).
- QPA: version 1.36, loaded from `~/.gap/pkg/qpa`, a git clone at
  `v1.36-20-g9100462`.
- Command: `cd "$(mktemp -d)" && /usr/bin/gap -q -T -m 1g
  .../tests/qpa-oracle/generate_fixtures.g` (23 fixtures written; schema v6),
  about 73 s of CPU time per run.
- SHA-256: `d4e3561f3d9b58111381d35da7b6c6d5174d33e3152a798f3d5724fb3a9dde0c`.
- Two completed runs in fresh temp dirs produced byte-identical output.
- The only change against the previous committed file (SHA-256
  `69f0c6d9e8f2505b0df4f46490df60c2c8573ac4eba8c42f2f6086cbc0b64428`,
  generated 2026-08-05 by the same tool chain) is the rename of the
  `yoneda_products` key `rank` to `yoneda_map_rank` in all 43 entries, the
  field name the v0.4 design binds. Renaming the key in the old file
  reproduces this one byte for byte.
- Every v5 field of every fixture is byte for byte the schema v5 file the
  2026-08-05 run replaced (SHA-256
  `b1a6222275a618623f61772b9b71d37ea139c9205a47369a338ff61c4732bf2a`).
  Deleting the v6 lines and restoring the schema string reproduces it exactly.

## Schema v6

Schema v6 is schema v5 unchanged, plus the Auslander-Reiten fields at the end of
every fixture, plus the schema string. The envelope keys are the same.

```json
{
  "schema": "auslander-qpa-oracle-v6",
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
      "ext": ["..."],
      "designated_modules": [{"kind": "simple", "index": 0}, "..."],
      "ar_sequences": [
        {
          "module": {"kind": "simple", "index": 0},
          "projective": false,
          "tau": [1, 1, 1, 0],
          "middle_dimvec": [2, 1, 1, 0],
          "middle": [{"dimvec": [1, 0, 1, 0], "multiplicity": 1}, "..."],
          "num_middle_summands": 2
        },
        {"module": {"kind": "simple", "index": 3}, "projective": true},
        "..."
      ],
      "irreducible_maps": [
        {
          "module": {"kind": "simple", "index": 0},
          "into": {
            "present": true,
            "total": 2,
            "sources": [{"dimvec": [1, 0, 1, 0], "valuation": 1}, "..."]
          },
          "out_of": {"present": false, "total": 0, "targets": []}
        },
        "..."
      ],
      "ext_algebra": {
        "module": "sum-of-simples",
        "max_degree": 4,
        "dims": [4, 4, 1, 0, 0],
        "min_generators": [4, 4, 0, 0, 0],
        "product_rank": [0, 0, 1, 0, 0]
      },
      "yoneda_products": [
        {
          "i": 0, "j": 1, "k": 3,
          "dim_ext1_ij": 1, "dim_ext1_jk": 1, "dim_ext2_ik": 1,
          "yoneda_map_rank": 1
        },
        "..."
      ],
      "stable_hom": [[1, 0, 0, 0, "..."], "..."],
      "tau_rigid": [true, "..."],
      "rigid": [true, "..."],
      "tau_period": [{"none_up_to": 6}, "..."]
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

Auslander-Reiten fields, new in v6. They all run over one fixed list:

- `designated_modules`: every simple `S_i` as `{"kind": "simple", "index": i}`,
  then every indecomposable projective `P_i`, then every indecomposable
  injective `I_i`, in vertex order, so the list has `3 * num_vertices` entries.
  They come from `SimpleModules`, `IndecProjectiveModules` and
  `IndecInjectiveModules` in that order. A module is named by kind and index and
  never looked up by its dimension vector: on `kronecker-2` the dimension
  vector `[1, 1]` belongs to `field + 1` pairwise non-isomorphic modules, so a
  dimension vector does not identify anything there. A module that is both
  simple and projective is listed twice, once per kind, and both entries carry
  the same results.
- `ar_sequences[m]`: the almost-split sequence ending at designated module `m`,
  from QPA's `AlmostSplitSequence(M, "r")`. `"projective": true` records that
  QPA returned `fail`, which happens exactly on the projectives; the other
  fields are then absent. Otherwise `tau` is the dimension vector of the start
  term, checked against `DTr(M)` during generation, `middle_dimvec` is the
  dimension vector of the middle term, `middle` lists its Krull-Schmidt
  summands as dimension vectors with multiplicities (sorted, equal dimension
  vectors merged, as in `decomposition`), and `num_middle_summands` counts them
  with multiplicity.
- `irreducible_maps[m]`: the irreducible morphisms into and out of `m`. `into`
  reports `IrreducibleMorphismsEndingIn`, `out_of` reports
  `IrreducibleMorphismsStartingIn`. `present` is false exactly where QPA has no
  such morphism to offer: a projective with zero radical has nothing ending in
  it, and an injective equal to its socle has nothing starting from it. `total`
  counts the morphisms, and `sources` (resp. `targets`) lists the endpoint
  dimension vectors, sorted, with `valuation` the number of morphisms merged
  into that entry.
- `ext_algebra`: `ExtAlgebraGenerators(A/rad, max_degree)` on
  `A/rad = sum of all simples`. `dims[k]` = `dim Ext^k(A/rad, A/rad)` for
  `k = 0..max_degree`, `min_generators[k]` counts the minimal generators of the
  Yoneda algebra in degree `k`, and `product_rank` is the elementwise
  difference: the rank of the multiplication into degree `k`. Only this module
  is reported, because `rad End(A/rad) = 0` makes the difference the genuine
  Yoneda product rank.
- `yoneda_products`: one entry per ordered triple of simple indices with
  `dim Ext^1(S_i, S_j) > 0` and `dim Ext^1(S_j, S_k) > 0`. `yoneda_map_rank`
  is the rank of the image of
  `Ext^1(S_i, S_j) x Ext^1(S_j, S_k) -> Ext^2(S_i, S_k)` in
  `Ext^2(S_i, S_k)`, whose dimension is `dim_ext2_ik`. The three dimensions
  repeat values that `ext` already stores, which cross-checks the two routes.
- `stable_hom[a][b]` = `dim Hom(M_a, M_b)` minus the dimension of the subspace
  of morphisms that factor through a projective, over designated modules `a`
  and `b`.
- `tau_rigid[m]` and `rigid[m]`: `IsTauRigidModule` and `IsRigidModule`.
- `tau_period[m]`: `{"period": i}` when `DTr^i(M) = M` for the smallest such
  `i` inside the bound, else `{"none_up_to": bound}`. The bound is 6 for every
  fixture except `inclusion-ambiguity`, where it is 3: the tau orbit of the
  simple module there has dimensions 1, 8, 26, 86, 284, and the fifth step
  alone costs over a minute. A value never claims a larger bound than it
  checked.

Schema history: v1 through v4 stored one implicit global field and untyped
values. v5 added the per-fixture field and presentation. v6 adds the
Auslander-Reiten fields above and changes nothing else. The reader rejects
every schema string it does not implement, so a stale oracle file fails loudly
instead of silently skipping checks.

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
committed file is equal to `commutative-square` `f5`, on the v5 fields and on
the v6 fields alike, verified after generation.

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

The v6 fields separate the two cases further. `ext_algebra` and `rigid` agree;
`ar_sequences`, `irreducible_maps`, `yoneda_products`, `stable_hom`,
`tau_rigid` and `tau_period` differ. The sharpest three:

- `yoneda_products`: the triple `(S_0, S_2, S_3)` has `yoneda_map_rank` 0
  over F_2 and 1 over F_3, from equal factor dimensions `1, 1` into an equal
  `dim Ext^2 = 1`. The product of two nonzero Ext classes dies in one
  characteristic and survives in the other.
- `tau_period`: `S_1` is tau-periodic with period 2 over F_2 and has no period
  up to 6 over F_3.
- `tau_rigid`: `I_3` is tau-rigid over F_3 and not over F_2, which is the
  same degeneration that makes `I_3` projective over F_3 only.

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
