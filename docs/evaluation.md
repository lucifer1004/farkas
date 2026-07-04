# Evaluation

This document is the single source of truth for every performance and
correctness claim made by this project: what was measured, under which
conditions, and what would invalidate the conclusions. Numbers elsewhere
(README, docs/grind.md) are excerpts of this document.

## 1. Experimental setup

**Artifact.** farkas at the commit tagged in each table; Lean 4 / Mathlib
pinned to v4.31.0 throughout. All Lean-side measurements use the shadow
elaborators of `Farkas.Instrument`, whose telemetry timestamps are
monotonic nanoseconds.

**Reference corpus.** 438 Lean files (one theorem each) from
DeepSeek-Prover-V2's published miniF2F solutions — machine-generated
proofs, i.e. the distribution a prover farm actually emits. Under
Mathlib v4.31.0, 259/438 compile cleanly; the remainder fail from version
drift and are retained (failing tactic calls are part of the workload).
The corpus regenerates bit-identically from its public source
(`docs/corpus.md`). Volume: 2,910 `(n)linarith` invocations, 4,599 oracle
calls, problem sizes up to 13k nonzeros and integer coefficients up to
~10^606 (607 decimal digits).

**Environment.** One x86-64 workstation (16 physical cores). Same-machine,
same-day runs are compared; observed run-to-run wall-clock variance for
identical workloads is ≈5% (§9), which bounds what file-level comparisons
can resolve.

**Regimes.** Three measurement granularities are used and must not be
conflated:

- *tactic-level*: per-invocation wall time of `(n)linarith` from telemetry;
- *batch*: `lake env lean <file>` per file — every file pays Mathlib import
  (~40 s), which dominates file wall clock;
- *live-REPL*: one persistent REPL per worker, Mathlib imported once, each
  theorem submitted incrementally — measures the *marginal* cost per
  theorem, the quantity that snapshot/keep-alive prover infrastructures
  expose. 4 workers, REPL restart every 40 theorems.

## 2. Oracle replacement

The Rust daemon (`farkas-oracled`) reimplements Mathlib's simplex
certificate search over tiered exact rationals (i64 → i128 → BigInt with
checked promotion; 99.94% of arithmetic operations remain in the i64 tier
on the reference corpus).

| metric (reference corpus) | stock (interpreted) | native daemon |
|---|---|---|
| oracle call, median | 4.18 ms | 0.43 ms |
| single-thread throughput (microbenchmark, all 4,599 calls) | 1× | 107.8× |

The per-call speedup through the pipe (~10× at the median) is smaller
than the microbenchmark ratio because the daemon path pays ~0.4 ms of
IPC per call — the engine itself accounts for well under 0.1 ms at the
median.

## 3. End-to-end ladder (live-REPL regime)

All three rows measured back-to-back on the same day (2026-07-03), full
corpus, identical worker configuration. Every row reproduced identical
behavior: 259/438 files clean, 2,878/2,910 invocations succeeded.

| configuration | (n)linarith time | marginal end-to-end |
|---|---|---|
| stock Mathlib | 893 s | 1,802 s |
| + native oracle | 655 s | 1,567 s |
| + probe-then-restrict fast path | **328 s (−63%)** | **1,236 s (−31.4%)** |

In this regime `(n)linarith` is 893/1,802 ≈ 50% of marginal compute —
the Amdahl bound on any linarith-side optimization.

Ablation: restricting the fast path to plain-form invocations (no
`[args]`/`only` coverage) measures −47% / −22.1% on the same corpus —
covering the `[args]`/`only` forms (§4's hit-rate definition spans all
three forms) accounts for the remaining delta.

## 4. Fast-path coverage

**Definition.** *Hit rate* = fraction of `(n)linarith` invocations that
the fast path closes itself (probe → certificate → restricted stock run
succeeds), over the invocations that stock also closes. Missed
invocations fall back to the stock path at full cost plus one probe
(median probe cost ≈ 0.5 ms). On hits, the selected set is tiny: median
1 hypothesis, p90 = 3, max 13 (full corpus, 2,716 hits).

**Distributions.** Because the probe re-implements stock preprocessing
semantics numerically, its coverage was tuned on the reference corpus and
must be validated off-distribution. Three test sets:

| distribution | hit rate |
|---|---|
| reference corpus (tuning set), full 438 files, 2,878 invocations | 96.2% |
| Mathlib source files (14 linarith-dense modules, 354 invocations) | 82.5% |
| `MathlibTest/Tactic/Linarith` (adversarial suite) | 76.8% |

**§4.1 Overfit audit.** Because the tuning corpus is concretely typed,
the probe was audited for corpus-shaped assumptions by measuring the
off-distribution sets independently. The audit's main catch: a type
whitelist (ℕ/ℤ/ℚ/ℝ) that blacked out generic-field modules entirely
(one at 0/21) and cost 5–10 points on every off-distribution set. It
was removed — the probe is type-agnostic by construction (atoms are
opaque; ℤ/ℕ retain their special semantics; a semantically wrong probe
merely mis-selects and falls back) — and every distribution improved,
including the tuning set. Compile outcomes were identical before and
after every probe change.

**Residual misses** (all safe fallbacks): goals of unsupported shape
(`≠`, Boolean equality — stock linarith fails on these too), types with
truncating subtraction (e.g. `ℝ≥0`) where the probe's field-like model
mis-selects, and a probe-miss tail from atom-granularity mismatches with
stock's ring normalization.

## 5. Behavioral equivalence

Two independent gates, both required for every change:

1. **Differential gate** (`scripts/differential.py`): Mathlib's own
   linarith test files plus this project's corner suite are compiled as
   twins differing only by `import Farkas.Auto`; exit codes and full
   diagnostic output must be byte-identical. 3/3 files identical at every
   measured commit.
2. **Outcome parity**: every full-corpus replay must reproduce exactly
   259/438 clean files and 2,878/2,910 successful invocations. This held
   for every configuration reported here.

Equivalence is at the level of compile outcomes and diagnostics, not
proof terms; the fast path necessarily produces different (smaller)
elaboration traces.

## 6. Robustness

- **Protocol fuzzing** (`tests/daemon_fuzz.rs`): 24 structured
  malformations (each followed by a liveness re-check), 300 deterministic
  random-garbage rounds, 30,000-digit coefficients, a 1 MB non-JSON line,
  and EOF mid-request. Invariant: one JSON response per line, daemon
  never wedges, EOF exits cleanly. The fuzz suite found (and its cases
  now pin) two real defects: a panicking parse path and an unbounded
  `maxVar` allocation.
- **Concurrency/chaos** (`scripts/stress.py`): 300 theorems elaborated in
  parallel through one shared daemon — 300/300 closed, 100% hit rate,
  zero protocol errors. With the daemon killed every 0.4 s (6 kills):
  200/200 closed, still 100% hits — respawn plus handshake is invisible
  to callers. Volume: 1,000 theorems, ~8 ms marginal per theorem.

## 7. Necessity of exact arithmetic

The corpus tail makes floating-point solving unsound in both directions:
double-precision LP accepts near-solutions *and* reports exactly-feasible
instances infeasible (observed with FP64 HiGHS on a hypothesis row with
coefficients ≈3.2·10^29; one certificate weight in the corpus has 607
digits). An FP64-basis-identification + exact-repair hybrid engine was
implemented and measured: it loses to the pure tiered-exact engine on the
heavy tail and is retained in the source only as that counterfactual.
Consequently: certificates are exact-verified before leaving the daemon,
and "no certificate" answers only ever come from an exact engine.

## 8. Relationship to `grind`

See `docs/grind.md` for the standing analysis. Measured facts: textual
`linarith`/`nlinarith` → `grind` substitution over the reference corpus
gives grind 206/259 takeover (79.5%), 53 regressions (one a grind
search timeout at 30 min), 5 reverse gains. 46 of the 53 regressions
involve `nlinarith` — the successor's gap is the nonlinear product
heuristic; pure-linear takeover is ≈97%. File-wall speed comparisons between the variants are not
claimed: on the 206 both-clean files, total (n)linarith tactic time is
169 s inside a ~9,000 s import-dominated wall (<2%), below the ≈5%
run-to-run variance (§9). What telemetry does measure on that set:
stock linarith 169 s vs farkas 62 s at tactic level; grind exposes no
per-call telemetry, so its tactic time is not separable by wall
subtraction.
A synthetic context-sensitivity benchmark (40 theorems, 0/10/30 irrelevant
arithmetic hypotheses) shows grind's per-call cost rising ~45 ms → ~410 ms
at 30 junk hypotheses vs linarith's ~45 ms → ~295 ms: per-hypothesis cost,
the quantity the probe eliminates, is larger for grind.

**Fact-selection prototype** (`Farkas.GrindFast`, experimental): probe →
`tryClear` non-selected propositional hypotheses → `grind`, full-context
fallback on failure. On the 211 grind-clean reference-corpus files
(843 aligned call sites, telemetry timing): grind tactic time
132.6 s → 57.1 s (−57%, wrapper cost included), grind body alone
35.4 s (3.7×); probe+clear wrapper overhead 18.8 s ≈ 23 ms/call;
average 42.5 hypotheses cleared / 1.2 kept, 28 probe-misses, zero
fallbacks; compile outcomes identical (211/211).
Caveat: these are linarith-shaped, arithmetic-only goals — the
favorable case for clearing; goals that need cleared hypotheses for
instantiation would take the fallback.

## 9. Threats to validity

- **Single corpus family.** The reference corpus is competition
  mathematics (miniF2F) as solved by one prover. The off-distribution
  measurements (§4) partially address this; `docs/corpus.md` ships the
  harness so any workload can be measured instead of trusted.
- **Single machine; wall-clock noise.** Run-to-run variance for identical
  workloads is ≈5% of file wall clock. Only telemetry-based tactic-level
  comparisons and same-run A/B deltas cross that floor; wall-based
  speed claims between tactic variants are therefore not made anywhere
  in this document (§8).
- **Substitution-based grind comparison.** Textual tactic replacement
  measures grind on goals *shaped for linarith*; a native grind migration
  might restate goals and fare differently in either direction.
- **Equivalence scope.** Outcome- and diagnostic-level, not proof-term
  level (§5).
- **Coverage of generic mathematics.** The 82.5% Mathlib-source figure
  comes from 14 linarith-dense modules selected by call count, not a
  random sample of Mathlib.

## 10. Reproduction

```bash
# corpus (bit-identical to the reference)
scripts/farkas-corpus.py acquire --from-dsv2
# batch replay + report tables
scripts/farkas-corpus.py replay --src corpus/dsv2-download --out corpus/myrun
scripts/farkas-corpus.py report --run corpus/myrun
# live-REPL ladder rows
scripts/replay_live.py --oracle stock            # row 1
scripts/replay_live.py --oracle native           # row 2
scripts/replay_live.py --oracle native --fast    # row 3
# behavioral gates
scripts/differential.py
# coverage / miss buckets
scripts/fast_misses.py corpus/myrun
# stress
scripts/stress.py --n 300 && scripts/stress.py --n 200 --chaos
# grind successor watch
scripts/farkas-corpus.py grind-check --src corpus/dsv2-download --out corpus/gc
```
