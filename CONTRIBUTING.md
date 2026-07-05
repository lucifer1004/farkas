# Contributing to farkas

## Layout

| path | contents |
|---|---|
| `oracle/native/` | Rust: `farkas-core` lib (tiered exact engines, verifier), `farkas-oracled` daemon, `farkas-bench` dev tool |
| `lean/` | Lean package `farkas`: `Farkas/Native.lean` (daemon client), `Farkas/Fast.lean` (probe-then-restrict), `Farkas/Instrument.lean` (shadow elabs + opt-in telemetry), `Farkas/Auto.lean` (drop-in entry) |
| `docs/` | protocol spec, certificate-LP semantics spec, roadmap, release/corpus guides |
| `scripts/` | replay harnesses, corpus recipe (`farkas-corpus.py`), differential gate, drift check |

## Dev setup

Rust: any recent stable toolchain; `cd oracle/native && cargo test && cargo build --release`.

Lean: install [elan](https://github.com/leanprover/elan). Heads-up for machines
with small home quotas: Lean toolchains and Mathlib caches are large — point
`ELAN_HOME` and `XDG_CACHE_HOME` at a roomy disk *before* the first build:

```bash
export ELAN_HOME=/big/disk/elan
export XDG_CACHE_HOME=/big/disk/.cache
export PATH="$ELAN_HOME/bin:$PATH"
```

Then: `cd lean && lake update && lake exe cache get && lake build`.

## Testing & linting

* Rust: `cargo test`; CI also gates `cargo clippy --all-targets -- -D warnings`
  (fixtures are checked in; no external corpus needed).
* Lean env linters: `cd lean && lake exe runLinter Farkas` (Batteries; docBlame
  etc. — public defs need docstrings). Build-time `linter.*` warnings should
  stay at zero in library code; test files may `set_option` them off when
  hypotheses are intentionally unused.
* Lean smoke: `FARKAS_NATIVE_BIN=$PWD/../oracle/native/target/release/farkas-oracled lake env lean tests/instrument_smoke.lean`
* Degradation check: the same file *without* `FARKAS_NATIVE_BIN` must still
  succeed (stock fallback + one-time note).
* Stress (parallel elaboration, daemon volume, kill/respawn chaos):
  `python3 scripts/stress.py --n 300` and `--chaos`; every theorem must
  close and (no-chaos) hit rate must stay >= 95%.

## Soundness rules (non-negotiable, enforced in review)

1. Certificates are proposals: every one must pass the exact BigRational
   verifier in Rust *and* stock linarith proof reconstruction in Lean.
2. A "no certificate" answer may only come from an exact engine.
3. The fast path may only *select hypotheses*; it never constructs proofs.
4. A missing/broken daemon must degrade to stock behavior, never fail a build.

## Sync with Mathlib

`Farkas/Instrument.lean` replicates the stock `linarith`/`nlinarith`
elaborator bodies and `Farkas/Fast.lean` mirrors preprocessing semantics
numerically. When bumping the Mathlib pin, re-diff
`Mathlib/Tactic/Linarith/{Frontend,Preprocessing,Verification,Datatypes}.lean` against
the previous pin and update the mirrors (CI drift check: `scripts/check-mathlib-drift.sh`; procedure in `docs/release.md`).
