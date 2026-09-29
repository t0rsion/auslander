# Public v0.10 validation

This record describes local v0.10.0 checks against the v0.9.0 baseline.
It does not record publication or cross-platform CI results.

## Functional scope

`classify_derived` partitions a finite family over one prime field up to
derived equivalence. A merge replays a tilting or silting mutation recipe
and checks an isomorphism onto the recovered target. A separation recomputes
one derived invariant. Every other pair is typed `Unresolved`. The committed
atlases cover the connected gentle algebras over `F_2` with at most 3 and at
most 4 vertices. The browser verifier replays them with the same Rust
verifier compiled to WebAssembly.

## Independent mathematical evidence

The live GAP/QPA oracle run passes: 109 tests. Every certified merge in the
4-vertex study agrees with the complete gentle invariant of Amiot,
Plamondon, and Schroll, and no separation contradicts a merge. A seeded
mutation test tampers with every committed artifact and parity fixture and
checks that no semantically changed document verifies.

## Source review

The production-line scanner measures 47006 code lines, against 42336 at
v0.9.0. The release ceiling equals the measured release count.

The complexity audit records 604 maintained source files and 147120
physical lines, against 537 files and 131006 physical lines at v0.9.0. These
counts include bindings, tests, examples, Python stubs, and GAP sources.

The audit measures 11335 callable scopes: 10550 in band 1-5 and 785 in band
6-10. Maximum callable complexity is 10. 19 macro templates have maximum
complexity 8. No scope exceeds the policy ceiling.

## Local checks

| Check | Result |
| --- | --- |
| Quality-tool self-tests, line budget, and complexity | Pass |
| `cargo test --workspace` on Rust 1.92 | Pass |
| `cargo +1.88 test -p auslander -p auslander-wasm --no-run` | Pass |
| Clippy, all targets, warnings denied | Pass |
| Rustfmt | Pass |
| Rustdoc with warnings denied | Pass |
| Python test suite | Pass |
| WebAssembly and native verifier parity | Pass |
| Live GAP/QPA oracle | Pass |
