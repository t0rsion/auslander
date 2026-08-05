# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.0] - 2026-08-05

Decomposition, isomorphism, duality, and the Auslander-Reiten translate. Each
returns a machine-checkable witness or an explicit statement that no witness
was found.

### Added

- Opposite algebras, the k-dual `D`, and the Nakayama functor
  `ν = D ∘ Hom(−, A)`. `ElementMatrix` holds matrices over the algebra rather
  than over the field (`opposite`).
- `injective_envelope`, `coresolve`, and `injective_dimension`. A minimal
  injective coresolution is the k-dual of a minimal projective resolution over
  `A^op` and carries the same `ResolutionEnd` and `Bounded` status
  (`injective`).
- `EndoAlgebra`: `End(M)` as a structure-constant algebra with an exact
  Jacobson radical over `F_p` in every characteristic. The computation uses the
  Friedl-Rónyai chain and never trusts the trace form in small characteristic
  (`endo`).
- `decompose` and `krull_schmidt`: verified splittings. Each summand carries a
  `Certificate`, either `Indecomposable` or an honest `Undetermined`
  (`decompose`).
- `is_isomorphic`: an isomorphism verified by a checked two-sided inverse, or a
  proof of non-isomorphism as one of five `Obstruction` kinds (`iso`).
- `tau`: the Auslander-Reiten translate, computed two ways on every call and
  cross-checked: by the Nakayama kernel, and by transpose-then-dual over
  `A^op`. The routes share the minimal presentation and the element-matrix
  encoding and are independent downstream of it. A certified disagreement is
  `TauError::RoutesDisagree`; an undecided cross-check is
  `TauError::AgreementUnknown` (`ar`).
- `nakayama_indecomposables`: every indecomposable of a Nakayama algebra, each
  with its certificate (`enumerate`).
- Exact Dynkin and Euclidean recognition, the generalized Cartan matrix,
  positive roots, and `dynkin_indecomposables`, which constructs every
  indecomposable of a hereditary Dynkin path algebra through BGP reflection
  functors. Preconditions are typed errors (`dynkin`).
- QPA oracle schema v4: `tau`, `tau` of the injectives, and QPA-verified
  injective dimensions of the simples. The document reader is strict and
  rejects malformed input rather than skipping fields. Under `QPA_ORACLE=1`
  the comparison against live GAP output is byte for byte.
- Python bindings for the new decision surface: `decompose`, `krull_schmidt`,
  `is_isomorphic`, `tau`, injective envelopes, coresolutions and dimensions,
  projective covers, and the Dynkin and Nakayama enumerators, with `Resolution`
  exposing terms, maps, and augmentation, dual in shape to
  `InjectiveCoresolution`. The certificate, obstruction, and resolution-status
  types are exposed, not flattened. The lower-level machinery (`EndoAlgebra`,
  opposite algebras, the k-dual, `ElementMatrix`) stays Rust-only.

### Fixed

- `dynkin_quiver` and `euclidean_quiver` truncated vertex counts past the
  `u32` indexing of `Quiver` and silently built a small wrong quiver
  (`EuclideanType::A(2^32)` became a one-vertex loop). Both now return `None`
  when the diagram cannot be represented; the Python functions raise
  `ValueError`. The abstract counts stay mathematical: `num_vertices` and
  `indecomposable_count` answer over `usize`.
- `decompose` could not split a direct sum of isomorphic copies of a module
  over a large field. The idempotent search produced only central idempotents.
  Central idempotents separate Wedderburn blocks, so they cannot split
  `End(P^n) = M_n(k[x]/(x^d))`. The random Fitting fallback almost never drew a
  non-unit: a uniform element of `M_n(F_q)` is invertible with probability
  `1 - O(1/q)`. Non-units are now constructed rather than sampled, by splitting
  the minimal polynomial of a drawn element into coprime factors with
  Berlekamp's algorithm. A base-field root does not suffice: when the residue
  field is a proper extension `F_{p^d}`, as for `End(W ⊕ W)` with
  `End(W) = F_{p^d}`, a drawn element has a base-field eigenvalue with
  probability `O(p^(1-d))`, and the two irreducible factors that do split it
  can share a degree. The suite missed the defect because the decomposition
  tests ran only over F_2 and F_5.

## [0.1.0] - 2026-07-24

Initial release.

### Added

- Monomial bound quiver algebras kQ/I over checked prime fields, with
  finite-dimensionality certified at construction.
- Validated right modules; hom bases, kernels, cokernels; radical and socle
  series.
- Minimal projective resolutions and exact Ext in every degree, with typed
  partiality (`Bounded`, `ResolutionEnd`).
- QPA differential oracle with committed truth
  (`crates/auslander/tests/qpa-oracle/`).
- Python bindings (abi3, CPython >= 3.10) in `crates/auslander-py`.
