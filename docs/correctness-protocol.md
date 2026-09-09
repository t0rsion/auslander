# Correctness protocol

- Unit tests live in every module and are named after the fact they check. They
  include randomized dense-vs-sparse solver agreement and structural properties
  of resolutions: `d^2 = 0`, exactness of computed prefixes, and minimality.
- `crates/auslander/tests/fixtures.rs` holds twelve textbook fixtures (A_2, A_3,
  D_4, `k[x]/(x^2)`, `k[x]/(x^3)`, kA_3/(ab), Kronecker-2, a radical-square-zero
  cycle, three Nakayama algebras, a gentle tree algebra) with hand-derived
  dimensions, Cartan matrices, radical series, Ext tables, and projective and
  global dimensions. Each fixture runs over both F_2 and F_5. Two entries are
  regressions from an earlier in-house prototype. Hereditary Kronecker has
  global dimension exactly 1; the prototype's examples database claimed it
  infinite. Kupisch series [2, 2, 1] runs to completion; the prototype hung on
  it.
- `crates/auslander/tests/acceptance_nonmonomial.rs` runs the high-level
  operations over three non-monomial quotients: the commutative square
  `kQ/(ab - cd)` over F_5, the preprojective algebra of A_3 over F_2, and the
  inhomogeneous `kQ/(ab - cde)` over F_5. Each pinned value is hand-derived on
  the test that uses it, and the values that the oracle also stores agree with
  it.
- `crates/auslander/tests/residue_degree.rs` pins the field generality of the
  support tau-tilting layer. The completeness certificate needs no
  algebraically closed base field: every step holds for finite dimensional
  algebras over an arbitrary field. Approximation multiplicities are counted
  over the residue division ring `End(N_i)/rad End(N_i)`, not over the base
  field, so the certificate stays correct when that ring is larger. Over the
  prime fields this crate supports, that case cannot arise on the tau-tilting
  path: every approximation generator is a tau-rigid indecomposable, and over
  a finite field every tau-rigid indecomposable of `kQ/I` has residue degree
  1. The file carries that proof and its hypotheses. The residue arithmetic is
  exercised away from mutation instead, at degree 3 by a Kronecker fixture and
  at degree 2 by a non-hereditary one.
- `crates/auslander/tests/acceptance_ar.rs` pins the AR layer in two tiers.
  Ext spaces, the Yoneda product laws on every basis tuple within the degree
  bound, extension round trips, and AR-duality almost-split sequences run on
  the full non-monomial matrix. AR quivers, catalog witnesses, and arrow
  valuations run where an exhaustive catalog exists, with the almost-split
  sequences of `k[x]/(x^3)`, linear A_3, the commutative square, and
  preprojective A_3 pinned against hand-derived terms.
  `tests/mutation_ar.rs` feeds every reachable witness verifier tampered data
  and requires rejection. `tests/determinism_ar.rs` checks a fresh-process
  fingerprint and compares the committed golden AR-quiver renderings under
  `tests/golden-ar/` byte for byte.
- The verifier is tested against a tamper corpus: a wrong schema string, a
  composite field, an out-of-range arrow, a non-canonical coefficient, a
  non-monic or non-reduced basis, an origin expansion that gives the wrong
  value, membership traces with dropped steps, forged contexts, absent words and
  non-eliminating coefficients, missing, extra, duplicated and misplaced
  ambiguities, and normal-word lists with a missing word, an extra word, or the
  wrong order. Every one is rejected with its own error.
- Certificate bytes are byte-identical across two constructions in one process
  and across two fresh processes.
- Facts that are characteristic-free are checked over a large prime as well as
  over F_2 and F_5. Small fields hide failure modes that depend on how rare
  units are. A decomposition defect survived the suite because every test ran at
  F_2 and F_5: there a random endomorphism of `P ⊕ P` is a non-unit often enough
  to split by luck.
- `crates/auslander/tests/qpa-oracle/` is a differential harness against QPA
  under GAP. The committed `qpa_expected.json` was produced by a real GAP+QPA
  run (provenance in `crates/auslander/tests/qpa-oracle/README.md`), and an
  always-on test compares the library against it. Every fixture carries its own
  prime field and its coefficient-bearing relations, so the non-monomial cases
  are compared like the monomial ones. A missing or corrupted file is a hard
  failure, and regression tests pin the corruption checks.
  `native_snapshot.json` is a drift snapshot of the library's own output, not an
  oracle. Setting `QPA_ORACLE=1` invokes GAP itself and fails hard if GAP or QPA
  is unavailable or any value disagrees.
