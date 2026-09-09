# Release quality review

Run the quality review before each release. Keep the audit JSON with the
release evidence when the source scope changes.

```sh
python tools/check_complexity.py --self-test
python tools/check_text_line_budget.py --self-test
python tools/check_text_line_budget.py
python tools/check_complexity.py --json quality-complexity.json
```

The complexity policy is fixed. Leave scopes in bands 1-5, refactor scopes in
bands 6-10 when they are touched, refactor bands 11-15 now, and split scopes
above 15. The quality gate rejects callable and macro template complexity above
10. Review the audit's `source.physical_loc`, language counts, bands, maximums,
and violations against the preceding release. Use measured JSON values in the
release record.

The Rust and Python callable rows use `rust-code-analysis-cli` 0.0.25 and report
direct McCabe complexity after nested callable spaces are removed. The GAP rows
use the source tokenizer. They cover `function` definitions and `->` closures;
they do not execute GAP or claim runtime complexity. Rust macro rows measure
templates before expansion. The audit counts invocations and marks expanded
complexity as unmeasured. Invocation output is outside the gate's measured
bound.

The text budget checks maintained Rust, Python, Python stub, Markdown, TOML,
YAML, and shell files at most 700 lines. GAP and JSON files do not enter this
budget. Generated directories and private `paper-*-private` directories are
excluded. Do not remove tests, proofs, or meaningful code to satisfy the
budget. Remove duplicate code only when behavior stays typed and checked.
Preserve proof comments and test coverage. Apply the repository writing style
to changed comments, docstrings, and documents.

Review changed abstractions for duplicate state, forwarding layers, and repeated
validation. Keep each abstraction tied to a distinct contract. Do not compress
statements or remove whitespace to lower line counts. Remove unnecessary code
and record the measured change in production code lines.

Inspect source archives and wheels for private paths, contact details, and
unnecessary development references. Keep package and schema versions, toolchain
pins, and license attribution. For a local wheel, remap the home and repository
paths before compiling:

```sh
RUSTFLAGS="--remap-path-prefix=$HOME=/build-home --remap-path-prefix=$PWD=/source" \
  maturin build --manifest-path crates/auslander-py/Cargo.toml --release --strip
```

Run this command from the repository root. Check the resulting archive and
extension for private paths before using them as release artifacts.
