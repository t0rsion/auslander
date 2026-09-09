# QPA oracle schema and result reference

This guide records the committed schema, provenance, field meanings, and
comparison rules. Return to the [QPA oracle README](./README.md) for setup, live
runs, and regeneration.

## Provenance of the committed `qpa_expected.json`

The committed file records the GAP version, QPA version, and generator command
in its `provenance` object. Its SHA-256 is
`42b35124c9a9e399ff48b27ff2292df218afde357ab7e9a8badbbee9ec8a2c35`.

Two completed runs in fresh directories produced byte-identical output. QPA's
own list order is discovery order, so the generator sorts every emitted list
by an explicit key first. The recorded command contains executable flags, but
no temporary directory or absolute generator path.

## Schema v6

Schema v6 is schema v5 unchanged, plus the Auslander-Reiten fields at the end of
every fixture, plus the schema string. The envelope keys are the same. The
oracle is at v9 and carries the schema string `auslander-qpa-oracle-v9`; the v6
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
  degenerates over F_2 (see [fixture-reference.md](./fixture-reference.md)).
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
Auslander-Reiten fields above. v7 adds the support tau-tilting block below.
Schema v8 replaces its unread one-tilting list with designated classical
tilting candidates. Schema v9 adds their target invariants. The reader
implements two schema strings, v9 for the oracle and v6 for the snapshot. It
rejects every other string, so a stale file fails instead of skipping checks.
Each file is validated against exactly one of the two.

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
  vertex subset and the module summand dimension vectors sorted. This is a weak
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
  computing method, and a false answer never sets it.
  `ClassicalOneTiltingModule` is unavailable in the current crate, so nothing
  compares this field. The generator keeps writing it because the committed
  document must stay byte-identical to the run that produced it, and schema v8
  drops both together.
- `exchange_graph_self_consistency`: degree histogram, edge count and
  connectivity of the graph on the enumerated pairs, two pairs adjacent when
  they share `n - 1` of their `n` labels. It is computed from the enumerated set
  by label intersection, so it repeats what the enumeration already said. It is
  a self-consistency check, not external truth, and the key name says so. Every
  closed fixture came out exactly `n`-regular and connected.

The walk cap is a budget, not a claim. The not-closed marker records it.
Twenty-one of the 24 fixtures close, the largest at 17 indecomposables
(`inhomogeneous`), so their cap of 40 never binds. `kronecker-2`,
`self-overlap` and `inclusion-ambiguity` never close, and the cost of failing
grows steeply: at cap 12 the walk fails after 2.0 s, 40.4 s and 4.8 s
respectively, while at cap 16 `self-overlap` alone costs 380 s. Those three
carry cap 12. `brute_agreement` is available and true on all 20 closed
fixtures.

`d4-star` has 50 pairs with
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
  an exhaustive catalog exists, which is 11 of the 24 fixtures. Where it does
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
in 314 ms, the largest. All eleven match GAP's counts.

## Schema v8 classical tilting

Schema v8 keeps every v7 value except `support_tau_tilting.one_tilting`. That
field used dimension-vector lists as module labels, and the harness did not
read it. Its replacement is a fixture-level `classical_tilting` list whose
modules are named by construction.

```json
"classical_tilting": [
  {
    "id": "a3-mod-ab-da-pd2",
    "construction": "I0+I1+I2",
    "bound": 2,
    "module_dimvec": [2, 2, 1],
    "qpa_tilting": true,
    "projective_dimension": 2,
    "coresolutions": [
      [[1, 1, 0], [1, 1, 0]],
      [[0, 1, 1], [0, 1, 1]],
      [[1, 0, 0], [1, 1, 0], [0, 1, 1], [0, 0, 1]]
    ],
    "coresolutions_exact": [true, true, true]
  }
]
```

The generator designates two constructions in three records. `linear-a3-pd1`
is the F_5 control `S0+P0+P2` over linearly oriented A3.
`a3-mod-ab-da-pd2` is `I0+I1+I2` over `A3/(ab)`, once over F_2 and once over
F_5. QPA builds each module from those constructors, then calls
`TiltingModule` at the recorded bound.

QPA 1.36 builds a finite coresolution after checking each approximation is
injective, but `HaveFiniteCoresolutionInAddM` does not check the last cokernel.
The generator therefore calls `IsExactSequence` on every returned complex and
stores `coresolutions_exact`. This includes exactness against the terminal zero
differential. The reader rejects a QPA-positive record if any entry is false.

The Rust comparison rebuilds the same candidate from its `id`, checks its
dimension vector, and runs `ClassicalTiltingModule::classify`. It compares the
projective dimension and the generation term dimensions. QPA lists each
per-projective complex from its last target back to the projective, so the
harness reverses those lists before it adds them term by term.

## Schema v9 targets

Schema v9 adds one `target` outcome to each QPA-positive classical-tilting
record. A computed outcome has this form:

```json
"target": {
  "status": "computed",
  "algebra": "endomorphism-opposite",
  "dimension": 5,
  "cartan": [[1, 0, 0], [1, 1, 0], [0, 1, 1]],
  "radical_layers": [3, 2],
  "simple_ext1": [[0, 0, 0], [1, 0, 0], [0, 1, 0]]
}
```

QPA computes `EndOfModuleAsQuiverAlgebra(T)`, then applies
`OppositePathAlgebra`. The result is `End_A(T)^op`, the target for right
modules. The generator records its dimension, Cartan matrix, dimensions of
`J^i/J^(i+1)`, and simple Ext^1 matrix. It does not record QPA's relation list.
The relation generators are not canonical.

QPA and auslander can order primitive idempotents differently. The comparator
therefore requires one vertex permutation to match both the Cartan and Ext^1
matrices. The same permutation applies to rows and columns. Dimension and
radical layers are order-independent and compare directly.

An unavailable QPA operation produces a typed outcome:

```json
{"status": "skipped", "reason": "operation-unavailable"}
```

The other accepted reasons are `endomorphism-presentation-failed`,
`opposite-algebra-failed`, and `invariant-computation-failed`. The strict
reader rejects every other reason. The three committed records are computed,
so the always-on gate runs `present_target` and requires `Presented` for each
one.
