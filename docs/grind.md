# farkas and `grind`

Lean core's `grind` ships its own linear-arithmetic solver
(`Grind.Arith.Linear`) and is the natural long-term successor to
standalone `linarith`. This note records the standing watch and which
farkas ideas transfer. All measured numbers, setup, and the noise-floor
analysis live in `docs/evaluation.md` §8/§9.

## Standing watch

```bash
scripts/farkas-corpus.py grind-check --src DIR --out RUN
```

substitutes `linarith`/`nlinarith` → `grind` over a corpus and diffs
per-file compile outcomes. Reference-corpus baseline (Lean v4.31,
2026-07-03): takeover 206/259; **46 of 53 regressions involve
`nlinarith`** — grind's gap is the nonlinear product heuristic, not
linear arithmetic. Re-run quarterly; migration pressure is real when the
`nlinarith` regressions disappear. Until then, the prover-emitted
`nlinarith` stream — where the farkas probe gains most (pairwise
products make stock preprocessing O(n²)) — is exactly the segment grind
does not yet cover.

## What transfers, what does not

`Grind.Arith.Linear` is an incremental model-search solver inside
grind's e-graph — constraints internalize as they are asserted, proofs
are built per step, and the code is native-compiled. Consequences:

- **The external oracle does not transfer.** There is no
  `CertificateOracle`-style boundary to plug into, and no interpreter
  gap to win back.
- **Probe-then-restrict transfers as *fact selection* — prototyped.**
  grind pays per hypothesis (30 irrelevant arithmetic hypotheses raise
  its per-call cost ~45 ms → ~410 ms; evaluation §8). The best a library
  can do without a hook is `clear`: `Farkas.GrindFast` (experimental)
  probes, clears non-selected propositional hypotheses, runs `grind`,
  and falls back on failure. Measured on the 211 grind-clean files of
  the reference corpus (843 call sites): grind tactic time 132.6 s →
  57.1 s (**−57%**, probe+clear cost included; grind body alone 3.7×
  faster; avg 42.5 hypotheses cleared, 1.2 kept; zero fallbacks).
  A native fact-gating hook would additionally remove the ~23 ms/call
  wrapper overhead and leave the e-matching context intact — the
  prototype is the lower bound. The daemon protocol is already
  tactic-agnostic (`docs/protocol.md`), so the same daemon serves.

## Practical stance

farkas accelerates the linarith that provers emit today; `grind-check`
watches the successor; the selection idea and the measurement harness
are on the table for whenever grind grows an extension point.
