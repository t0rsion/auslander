# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
