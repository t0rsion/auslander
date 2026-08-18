# QPA oracle

This harness compares the library's homological output against QPA, the GAP
package "Quivers and Path Algebras". QPA is an independent implementation with
two decades of use, so a disagreement points at one side or the other, not at a
shared assumption.

## Files

Two JSON files, produced by independent tool chains:

- `qpa_expected.json`: committed, at schema v7, and the oracle the harness
  reads. A real GAP+QPA run of `generate_fixtures.g` generated it. This library
  never writes it. The always-on test `library_matches_the_committed_qpa_truth`
  compares the library's freshly computed values against it, and a missing or
  unreadable file is a hard test failure, not a skip.
- `native_snapshot.json`: committed, at schema v6, and not an oracle. It is this
  library's own output, written by the test's `QPA_ORACLE_WRITE=1` mode. It is
  kept so that unintended drift in our values fails CI even without GAP
  installed. Agreement with it is self-consistency only. Correctness comes from
  `qpa_expected.json`. It stays at v6 because the v7 block holds
  `brute_agreement`, a GAP-internal cross-check with no library counterpart, and
  a snapshot must not invent one. The harness implements exactly these two
  schema strings and rejects every other, so neither file goes stale unnoticed.

`generate_fixtures.g` writes `qpa_generated.json` into its working directory,
which the `.gitignore` here covers. The name is deliberately not the oracle's,
so a run started in this directory cannot overwrite `qpa_expected.json`;
promoting a run is a separate copy.

## Test modes (`crates/auslander/tests/qpa_oracle.rs`)

| Mode | Trigger | Behavior |
| --- | --- | --- |
| Oracle comparison | always on | library values vs `qpa_expected.json`; missing file = failure |
| Snapshot self-consistency | always on | library output vs `native_snapshot.json`, byte for byte |
| Snapshot rewrite | `QPA_ORACLE_WRITE=1` | rewrites `native_snapshot.json` only, never `qpa_expected.json` |
| Live GAP run | `QPA_ORACLE=1` | runs `generate_fixtures.g` under GAP+QPA in a temp dir, requires the sentinel and the output file, then compares the fresh output against the library (values) and against `qpa_expected.json` (values, then byte for byte); fails hard when GAP is missing, QPA does not load, no output appears, or anything mismatches |

The harness computes every v6 field from the library and compares it entry by
entry. Designated modules are built by construction from their kind and index,
never looked up by dimension vector. Almost-split sequences come from
`almost_split`, and the `ArDualityWitness` of every sequence the harness builds
is rechecked before its values are used. The irreducible morphisms out of a
module are computed over the opposite algebra on its dual, which is the same
computation as the morphisms into a module: `opposite` keeps the vertex ids and
`dual` keeps the dimension vector, so the values compare directly.

The always-on modes take 2.7 s of wall clock over 92 tests, measured with
`cargo test -p auslander --test qpa_oracle`; the v6 layer alone took 2.45 s over
74 tests, so the whole v7 comparison costs about 0.3 s of wall clock and about
3 s of CPU that runs beside the corruption tests. The live run takes 322 s, all
but 3 s of it inside GAP. The workspace sets `opt-level = 2` for the dev
profile, because at `opt-level = 0` this suite takes over ten minutes locally
and stalls the Windows CI runner. Debug assertions and overflow checks stay on.
`inclusion-ambiguity` dominates the v6 layer: its almost-split sequences run on
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

GAP is invoked with `-q -T` and closed stdin, so an error quits the run instead
of hanging in a break loop. A QPA load failure is such an error. `-m 1g` asks
for a large initial workspace, which the workload needs (see below).

The exit code is not a failure signal. `gap -q -T` with closed stdin exits 0
after an uncaught error, measured for a division by zero, an unbound variable
and a QPA "no method found", so an `output.status.success()` assertion is
vacuous. `qpa_oracle.rs` checks the two signals that do carry:

- The generator writes its output in one final statement, after every value is
  computed and every byte formatted, so a run that dies leaves no output file.
- The last line of stdout is the sentinel `qpa-oracle-generator-ok`, printed
  after the write. An aborted run never reaches it.

## Regenerating the oracle

Only the GAP path may write these files:

```sh
cd "$(mktemp -d)"
/usr/bin/gap -q -T -m 1g \
   /path/to/crates/auslander/tests/qpa-oracle/generate_fixtures.g | tail -1
cp qpa_generated.json \
   /path/to/crates/auslander/tests/qpa-oracle/qpa_expected.json
```

The generator emits schema v7 and the last line must read
`qpa-oracle-generator-ok`. It writes `qpa_generated.json`, never
`qpa_expected.json`, so promoting a run is the deliberate copy above.

GAP 4.16dev crashes on this workload, with a segmentation fault and no message.
It crashed on two of five runs without `-m 1g` and on none of three runs with
it; the flag asks for a large initial workspace. The flag changes nothing in
the output: every completed run, with the flag and without, wrote the same
bytes. Raising the shell stack limit does not help; with
`ulimit -s unlimited` GAP crashed sooner. Use `-m 1g` and expect a v7 run to
take about 5.5 minutes. A crashed run leaves no output file, because the file is
written in one final statement, so a crash cannot produce a truncated file.
Repeat the run until it completes and prints the sentinel, then confirm two
completed runs in fresh directories agree byte for byte before copying either
one.

Then run the test suite and record the new provenance (below) in this README.
`QPA_ORACLE_WRITE=1 cargo +1.92 test --test qpa_oracle` regenerates
`native_snapshot.json` after an intentional library change. It never touches
`qpa_expected.json`.

## What reproducibility means here, and what it does not

Two claims live in `live_gap_run_agrees_with_library_and_committed_truth`, and
they are not the same strength.

The first is the mathematics: a real GAP+QPA run recomputes these values and
must agree with the library. That runs on ANY GAP and is asserted
unconditionally. It is the reason this oracle exists.

The second is reproducibility of this FILE, byte for byte. That holds only
within one GAP version. GAP 4.16dev and the Ubuntu distro package produce
documents that differ while both agree with the library, so the test compares
documents only when the fresh run's `gap_version` matches the one recorded
below, and otherwise reports the version gap and stops. A different GAP
therefore still gates the mathematics and cannot silently pass a wrong library.

The consequence for CI: `.github/workflows/qpa-oracle.yml` installs the distro
GAP, so it exercises the first claim and not the second. Pinning that workflow
to the recorded version, or regenerating the document on a pinned environment
so CI becomes the reference, is open work. Until then, do not read a green
oracle run as proof that this file reproduces on the runner.

## Provenance of the committed `qpa_expected.json`

- Generated: 2026-08-18, on Arch Linux, package `gap 4.16.0-2`
  (`/usr/bin/gap`, `GAPInfo.Version` = `4.16dev`).
- QPA: version 1.36, loaded from `~/.gap/pkg/qpa`, a git clone at
  `v1.36-20-g9100462`.
- Command: `cd "$(mktemp -d)" && /usr/bin/gap -q -T -m 1g
  .../tests/qpa-oracle/generate_fixtures.g` (23 fixtures written; schema v7),
  323 s and 319 s of wall clock in two fresh temp directories.
- SHA-256:
  `de3216e72b46c0b5cf311b8ba6219dbf5d260d1336d4b974baac516ae0f4d7b9`.
- Two completed runs in fresh temp dirs produced byte-identical output. QPA's
  own list order is discovery order, so the generator sorts every emitted list
  by an explicit key first.
- `provenance.command` inside the file reads `gap -q -T generate_fixtures.g`,
  the v6 spelling. It is a label the generator writes, not the command the run
  used; the command above is the run. It is left as generated, because the file
  is GAP output and this library never edits its bytes. A future GAP run may
  correct it.
- The previous committed oracle was schema v6 (SHA-256
  `d4e3561f3d9b58111381d35da7b6c6d5174d33e3152a798f3d5724fb3a9dde0c`, generated
  2026-08-06 by the same tool chain). Deleting the 23 `support_tau_tilting`
  blocks from this file, dropping the comma each preceding `tau_period` line
  gained, and restoring the schema string reproduces it byte for byte. Every v6
  field of every fixture holds the same value, and `schema` is the only
  top-level key that differs.
- The v6 file in turn differed from its 2026-08-05 predecessor (SHA-256
  `69f0c6d9e8f2505b0df4f46490df60c2c8573ac4eba8c42f2f6086cbc0b64428`) only in
  the rename of the `yoneda_products` key `rank` to `yoneda_map_rank` in all 43
  entries, and every v5 field matched the schema v5 file before that (SHA-256
  `b1a6222275a618623f61772b9b71d37ea139c9205a47369a338ff61c4732bf2a`).

## Schema v6

Schema v6 is schema v5 unchanged, plus the Auslander-Reiten fields at the end of
every fixture, plus the schema string. The envelope keys are the same. The
oracle is at v7 and carries the schema string `auslander-qpa-oracle-v7`; the v6
string below is the one `native_snapshot.json` carries, and the fields are the
same in both.

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
- `tau[i]`: the AR translate of `S_i`, either `{"projective": true}` when `S_i`
  is projective (the library tests the translate with `Module::is_zero`) or
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
  never looked up by its dimension vector: on `kronecker-2` over F_p the
  dimension vector `[1, 1]` belongs to `p + 1` pairwise non-isomorphic modules,
  so a dimension vector does not identify anything there. A module that is both
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
Auslander-Reiten fields above and changes nothing else. v7 adds the support
tau-tilting block below and changes nothing else. The reader implements two
schema strings, v7 for the oracle and v6 for the snapshot, and rejects every
other, so a stale file fails loudly instead of silently skipping checks. Each
file is validated against exactly one of the two.

JSON is written and read by hand: the schema is small and fixed, so string
formatting plus a strict recursive-descent reader replaces a serde dependency.
Only whitespace is free-form.

## Schema v7

Schema v7 is schema v6 unchanged, plus one `support_tau_tilting` block per
fixture, plus the schema string. The envelope keys are the same, and the v6
values are the same bytes.

QPA 1.36 has no support tau-tilting predicate, pair type, mutation, enumerator
or silting, so every value in the block is built from QPA primitives:
`HomOverAlgebra`, `DTr`, `IsTauRigidModule`, `MinimalLeftApproximation` and
`TiltingModule`. Nothing in it comes from this library.

```json
"support_tau_tilting": {
  "indecomposables": {"closed": true, "count": 12},
  "brute_agreement": {"available": true, "max_length": 5, "agrees": true},
  "tau_rigid_designated": [true, "..."],
  "total": 50,
  "histogram": [1, 4, 9, 16, 20],
  "pairs": [
    {"module_dimvecs": [[0, 0, 0, 1]], "projective_support": [0, 1, 2]},
    "..."
  ],
  "approximation_slots": 150,
  "approximations": [
    {
      "module_dimvecs": [[0, 0, 0, 1]], "projective_support": [0, 1, 2],
      "summand_dimvec": [0, 0, 0, 1], "source_dimvec": [0, 0, 0, 1],
      "target_dimvec": [0, 0, 0, 0], "rank": 0,
      "kernel_dimvec": [0, 0, 0, 1], "cokernel_dimvec": [0, 0, 0, 0]
    },
    "..."
  ],
  "one_tilting": [
    {
      "module_dimvecs": [[0, 0, 0, 1], "..."], "tilting": true,
      "projective_dimension": 0,
      "coresolutions": [[[1, 0, 0, 1], [1, 0, 0, 1]], "..."]
    },
    "..."
  ],
  "exchange_graph_self_consistency": {
    "degree_histogram": [0, 0, 0, 0, 50, 0], "edges": 100, "connected": true
  }
}
```

A fixture whose walk did not close carries the marker and nothing that depends
on it:

```json
"support_tau_tilting": {
  "indecomposables": {"closed": false, "cap": 12},
  "brute_agreement": {"available": false, "reason": "walk-not-closed"},
  "tau_rigid_designated": [true],
  "not_computed": {"reason": "walk-not-closed"}
}
```

- `indecomposables`: the typed closure marker of the AR-quiver walk, either
  `{"closed": true, "count": k}` or `{"closed": false, "cap": c}`. The walk
  seeds with `IndecProjectiveModules` and `IndecInjectiveModules`, closes under
  `IrreducibleMorphismsEndingIn` and `IrreducibleMorphismsStartingIn` behind the
  same two guards the `irreducible_maps` field uses, and deduplicates with
  `IsomorphicModules`. It never closes under `AlmostSplitSequence`: a
  projective-injective has no almost split sequence in either direction, and a
  walk that used it returned 1 indecomposable instead of 3 on `k[x]/(x^3)`. A
  finite closure certifies the list, because a finite AR component over a
  connected algebra forces representation-finiteness.
- `brute_agreement`: whether the walk and `AllIndecModulesOfLengthAtMost` at
  `max_length`, the largest length in the walk, produce the same isomorphism
  classes. The call is caught, because it errors when a length class below the
  bound is empty; that outcome is written `{"available": false, "reason":
  "gap-error"}`. It reads `walk-not-closed` where there is no walk to compare.
  This cross-check is what caught the incomplete closure operator above.
- `total` and `histogram`: the number of basic support tau-tilting pairs, and
  the count by module-summand count `m = 0 .. n`. Both are gated on the closure
  marker. A truncated walk still yields a plausible number, and an ungated total
  would be a silent undercount: on `kronecker-2` the length-3 truncation reports
  5 pairs.
- `pairs`: one entry per pair, with the projective support as a sorted 0-based
  vertex subset and the module summand dimension vectors sorted. This is a WEAK
  value field. Repetitions are preserved, never merged, and never read as
  multiplicity or identity: `cyclic-nakayama-3-3-3` has three pairwise
  non-isomorphic projectives that all have dimension vector `[1, 1, 1]`, so its
  pair list contains `[[0, 0, 1], [1, 1, 1], [1, 1, 1]]` where the repetition is
  two distinct summands. The v6 merging helper is not used here. The projective
  support is chosen vertex by vertex from the vanishing of `Hom(P_i, M)`, which
  the generator asserts against the zero support of `M`, so that identity is
  checked rather than assumed and the field is a redundancy check.
- `tau_rigid_designated`: `IsTauRigidModule` over the v6 `designated_modules`
  list, the same values as the v6 `tau_rigid` field, emitted inside the block so
  it reads standalone.
- `approximation_slots` and `approximations`: approximation invariants at a
  deterministic sample of (pair, module summand) slots. `approximation_slots` is
  how many slots the fixture has; the sample is 12 of them, or all of them when
  there are fewer. Slots are ordered by module-summand count, then the pair's
  dimension vectors, the summand dimension vector and the projective support,
  and the sample is taken at even stride through that order. Each entry reports
  `MinimalLeftApproximation(X, M/X)`: source and target dimension vectors, rank,
  kernel and cokernel dimension vectors. No mutated pair is emitted. QPA
  realizes the exchange only when the approximation is injective with a nonzero
  cokernel; on `d4-star` that holds for 50 of 150 slots, and in the other 100
  the cokernel is the right exchange partner only half the time, so a mutated
  pair would be our construction and not QPA truth.
- `one_tilting`: `TiltingModule(M, 1)` over the enumerated pairs with `n`
  summands, with the projective dimension and one coresolution per
  indecomposable projective, each as a list of term dimension vectors. Extract
  the terms with `LowerBound` and `UpperBound` guarded by `IsZeroComplex`:
  `LowestKnownDegree` returns minus infinity on a `FiniteComplex` and the range
  then fails. `IsTiltingModule` is never called: it is an attribute with no
  computing method, and a false answer never sets it. The crate cut
  `ClassicalOneTiltingModule` before v0.5.0, so nothing reads this field any
  more. The generator keeps writing it, because the committed document must
  stay byte-identical to the run that produced it, and schema v8 drops both
  together.
- `exchange_graph_self_consistency`: degree histogram, edge count and
  connectivity of the graph on the enumerated pairs, two pairs adjacent when
  they share `n - 1` of their `n` labels. It is computed from the enumerated set
  by label intersection, so it repeats what the enumeration already said. It is
  a self-consistency check, not external truth, and the key name says so. Every
  closed fixture came out exactly `n`-regular and connected.

The walk cap is a budget, not a claim, and the not-closed marker records it.
Twenty of the 23 fixtures close, the largest at 17 indecomposables
(`inhomogeneous`), so their cap of 40 never binds. `kronecker-2`,
`self-overlap` and `inclusion-ambiguity` never close, and the cost of failing
grows steeply: at cap 12 the walk fails after 2.0 s, 40.4 s and 4.8 s
respectively, while at cap 16 `self-overlap` alone costs 380 s. Those three
carry cap 12. `brute_agreement` is available and true on all 20 closed
fixtures.

Values worth knowing when reading the file: `d4-star` has 50 pairs with
histogram `[1, 4, 9, 16, 20]` over both F_2 and F_5, and its 20 tilting modules
of projective dimension at most 1 are exactly the `m = n` entry of that
histogram, which is two independent QPA routes agreeing. `linear-an-3` and
`linear-nakayama-3-2-1` have 14, `truncated-poly-3` has 2, and the two
`characteristic-sensitive` cases separate again: 56 pairs over F_2 from 14
indecomposables against 46 over F_3 from 11.

## What the harness compares in the v7 block

Every field is compared against a library route that is independent of QPA,
or skipped with a typed reason. One field is unread, `one_tilting`, and it is
named as such below; nothing else passes by being unread.

- `indecomposables`: a closed marker is compared against the catalog size where
  an exhaustive catalog exists, which is 10 of the 23 fixtures. Where it does
  not, the marker gates the rest of the block and nothing else reads it. A
  not-closed marker together with a catalog of ours is a mismatch, because a
  classification theorem would then contradict a failed walk.
- `total`, `histogram`, `pairs`: from `supporttau::enumerate_over_catalog` over
  `arquiver::IndecomposableCatalog::{nakayama, dynkin}` where a catalog exists,
  and from `taugraph::support_tau_tilting_graph` where it does not, which must
  then return `Closed`. Both routes reproduce every count and every pair record.
  The pair lists are compared as multisets of records, with repetitions
  preserved: the v6 merging helper is not used, and the reader rejects a merged
  repetition because the labels no longer add to `n`.
- `tau_rigid_designated`: from `taurigid::is_tau_rigid` over the designated
  modules. The reader separately pins the list to the v6 `tau_rigid` field, so
  the two spellings cannot drift apart.
- `approximations`: each sampled slot is matched against every slot of ours with
  the same pair record and summand dimension vector, and the recorded invariants
  must occur among ours. A pair record is a weak identity, so the match is a set
  and not a lookup. Each slot recomputes `approx::left_approximation`.
- `one_tilting`: nothing. The reader accepts the key and drops the value, and
  no comparison route exists, because the crate cut the type that produced our
  side. Schema v8 removes the field from the generator and from the document
  in one deliberate regeneration.
- `exchange_graph_self_consistency`: recomputed from our own enumerated set by
  label intersection, where a label is the isomorphism class of a module summand
  or a projective vertex. Summand classes come from `is_isomorphic` inside a
  class of equal dimension vectors, so `cyclic-nakayama-3-3-3` gets three labels
  for its three projectives of dimension vector `[1, 1, 1]`. Both sides compute
  this from a pair list they already hold, so it is a self-consistency check and
  never external truth. The harness names it so.
- `brute_agreement`: read and validated, never compared. It is GAP's own
  cross-check of the walk against `AllIndecModulesOfLengthAtMost` and has no
  library counterpart.

The three fixtures whose walk did not close carry no total, no histogram and no
pair list, so nothing gated on completeness is compared there. Their closure
marker is compared, and `kronecker-2` gets the truncation cross-check in
`kronecker_2_truncates_on_both_sides`: both catalog constructors reject the
algebra, and a mutation-graph walk with `max_vertices = 16` returns a typed
`Incomplete` whose certified part rechecks. The ceiling is small because the
cost of failing grows steeply on a tau-tilting infinite algebra: the modules
on the preprojective ray grow without bound. The figures that once stood here
measured a work-unit rate this code no longer uses and are not restated.

`self-overlap` and `inclusion-ambiguity` are different. Both are local, so
`n = 1`, and a mutation-graph walk closes on each in under 0.3 ms with 2 pairs,
measured off the harness. GAP's AR-quiver walk did not close on either. There is
no conflict: GAP's walk enumerates indecomposable modules, ours certifies pairs
by left mutation, and neither implies the other. The oracle holds no total, no
histogram and no pair list there, so the harness compares none and does not walk
the graph.

The mutation-graph route runs with `max_vertices = 512` and otherwise the
default `MutationGraphLimits`. Every fixture that needs it closes: `gentle-tree`
37 pairs in 24 ms, `preprojective-a3` 24 in 18 ms, `commutative-square` 46 in
38 ms, `characteristic-sensitive` 56 over F_2 in 68 ms, and `inhomogeneous` 152
in 314 ms, the largest. All ten match GAP's counts.

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
`"convention": "right"` and the comparison is index for index. To mark a file
produced under a left-module setup, set `"convention": "left"`. The comparator
then transposes Cartan matrices, swaps the `(i, j)` Ext indices, and reads the
`tau` rows as tau over the opposite algebra before comparing. Left modules over
`A` are right modules over `A^op`, every directed pairing flips, and tau of a
left module is tau over `A^op`. The archived predecessor of this library used
the left convention, which is where its `Ext^1(S_sink, S_source)` values came
from.

The frozen archive repo carries vendored GAP and QPA source trees under
`external__gap/` and `external__qpa/`. Build them for a local installation when
no system GAP is available. `external__qpa/` is a valid `$QPA_DIR`.
