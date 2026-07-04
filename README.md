# farkas

**Fast, exact Farkas-certificate oracle and lazy preprocessing for Lean's
`linarith`.** Farkas' lemma says the certificate exists; this package finds it
fast.

Measured on a real LLM-prover workload — 438 miniF2F proofs as emitted by
DeepSeek-Prover-V2, 2,910 `(n)linarith` invocations, live-REPL regime
(Mathlib imported once, marginal cost per theorem); full setup, definitions
and threats to validity in `docs/evaluation.md`:

| configuration | (n)linarith time | marginal end-to-end |
|---|---|---|
| stock Mathlib | 893 s | 1,802 s |
| + native oracle | 655 s | 1,567 s |
| + probe-then-restrict fast path | **328 s (−63%)** | **1,236 s (−31%)** |

The fast path closes 96% of invocations on this workload (82% on
linarith-dense Mathlib source modules; hit rate is defined over the
invocations stock also closes), including `linarith [args]` and
`only [...]` forms; misses fall back to stock at full cost plus ~0.5 ms.
Oracle calls: median 4.2 ms → 0.4 ms. Behavioral equivalence is enforced,
not hoped for: identical compile outcomes on every full-corpus run and
byte-identical diagnostics on Mathlib's own linarith test suite
(`scripts/differential.py`).

## How it works

1. **Native exact oracle** (`farkas-oracled`, Rust): the same simplex
   certificate search Mathlib runs interpreted, re-implemented over tiered
   exact rationals (i64 → i128 → BigInt; 99.94 % of operations stay in i64).
   Spoken to over a local stdin/stdout daemon — no network, no services.
2. **Probe-then-restrict fast path**: hypotheses + negated goal are parsed
   *numerically* (no proof terms, no ring normalization), the oracle
   identifies the few hypotheses participating in the contradiction
   (median selected set: 1 hypothesis, p90 = 3), and stock `linarith only [...]`
   re-runs on that subset — the per-hypothesis proof-term preprocessing
   that dominates stock's cost is paid only for the selected few. Any
   failure at any step falls back to the stock path.

**Soundness:** the fast path only selects hypotheses; every proof is still
built by stock linarith and checked by the Lean kernel. Certificates are
exact-verified twice (Rust BigRational verifier + proof reconstruction).
A wrong oracle answer can cause a tactic failure, never a wrong proof.

## Quickstart

```toml
# lakefile.toml — the Lean package lives in this repo's lean/ subdirectory
[[require]]
name = "farkas"
git = "https://github.com/lucifer1004/farkas"
rev = "v4.31.0-farkas.1"   # pick the tag matching your Mathlib release
subDir = "lean"
```

```bash
lake update farkas
lake exe farkas-fetch   # prebuilt daemon → .lake/farkas/ (sha256-verified;
                        # needs a published release — see below to build instead)
```

```lean
import Farkas   -- drop-in: linarith/nlinarith are accelerated, scripts unchanged
```

Supported prebuilt targets: linux x86_64/aarch64 (musl-static),
macOS aarch64/x86_64, windows x86_64. Elsewhere — or if you prefer building
from source:

```bash
cd oracle/native && cargo build --release
export FARKAS_NATIVE_BIN=$PWD/target/release/farkas-oracled
# Windows (PowerShell):
#   $env:FARKAS_NATIVE_BIN = "$PWD\target\release\farkas-oracled.exe"
```

The daemon binary is discovered via `FARKAS_NATIVE_BIN` → the
`.lake/farkas/` artifact slot → `PATH`.

No binary? Everything still works — you get stock linarith plus a one-time
note. Use the oracle explicitly with `linarith (oracle := Farkas.native)`.

Environment variables (all optional):

| variable | effect |
|---|---|
| `FARKAS_NATIVE_BIN` | daemon binary path (overrides discovery) |
| `FARKAS_FAST=0` | opt out of the fast path (stock behavior) |
| `FARKAS_FAST_DEBUG=1` | per-miss diagnostics into the telemetry file |
| `FARKAS_ORACLE=native` | swap the oracle on the stock path too (A/B) |
| `FARKAS_CORPUS_FILE` | JSONL telemetry sink (off when unset) |
| `FARKAS_SRC` | source tag for telemetry rows (harness use) |
| `FARKAS_FETCH_TAG` / `FARKAS_FETCH_BASE_URL` | `farkas-fetch` overrides |

## Docs

* `docs/evaluation.md` — every claim above with setup, definitions,
  and threats to validity
* `docs/protocol.md` — daemon protocol (v1)
* `docs/release.md` — version policy (`v<mathlib>-farkas.<n>`), release process
* `docs/corpus.md` — reproduce the benchmark / measure your own workload
* `docs/certificate-lp-spec.md` — exact certificate semantics, validated
  against 4548 Mathlib-produced certificates
* `docs/roadmap.md` — status and the road to Mathlib/ecosystem integration
* `CONTRIBUTING.md` — dev setup, soundness rules, Mathlib-sync notes

## Limitations

Speedups are bounded by `(n)linarith`'s share of your workload (≈50% of
marginal compute on the reference corpus; likely less elsewhere — measure
yours with `docs/corpus.md`). The reference numbers come from one corpus
family and one machine; goals over types with truncating subtraction
(`ℝ≥0`) and `≠`-shaped goals currently always take the fallback path.
Lean core's `grind` is the long-term successor to linarith — measured
relationship and standing watch in `docs/grind.md`.

## Status

Pinned to Mathlib v4.31.0. Pre-release (0.1.x): interfaces may change while
the upstreaming conversation (docs/roadmap.md) is in flight.
