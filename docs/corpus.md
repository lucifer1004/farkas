# Corpus recipe — reproduce the benchmark, bring your own workload

(The measurements this corpus feeds are specified and qualified in
`docs/evaluation.md`.)

The measured numbers in the README come from replaying real LLM-prover
output (DeepSeek-Prover-V2's miniF2F solutions) with the farkas
instrumentation active. **The public repo ships the recipe, not the data**:
the solution files' redistribution license is unclear, so
`scripts/farkas-corpus.py` regenerates the corpus from the official source
at runtime, and only statistics (histograms, timing tables) live in docs.

## Reproduce the reference corpus

```bash
scripts/farkas-corpus.py acquire --from-dsv2          # official zip -> corpus/dsv2-download (gitignored)
scripts/farkas-corpus.py replay --src corpus/dsv2-download --out corpus/myrun --jobs 8
scripts/farkas-corpus.py report --run corpus/myrun    # size/timing tables + cert validation
```

Expected contents (checked 2026-07-03): 438 `.lean` files, 221 `valid/` +
217 `test/`.

## Bring your own workload

Any directory of Lean proof files works as `--src` — your RL traces, your
prover's outputs, your project. This is the recommended path for prover
farms: numbers measured on *your* workload beat ours.

```bash
scripts/farkas-corpus.py replay --src /path/to/your/proofs --out corpus/mine
```

`--from-mathlib` uses Mathlib's own linarith test files as a zero-license
smoke source (they are already on disk after `lake build`).

## Live-REPL measurements

`scripts/replay_live.py` (the marginal-cost regime of `docs/evaluation.md`)
additionally needs [leanprover-community/repl](https://github.com/leanprover-community/repl)
built at this repo's `lean-toolchain`; point `FARKAS_REPL_BIN` at the
built binary.

## Outcome differential

```bash
scripts/farkas-corpus.py diff --src DIR --out RUN
```

replays every file twice — stock (no farkas import) and fast — and requires
identical per-file compile outcomes. This is the corpus-scale complement to
the per-PR diagnostic-exact gate (`scripts/differential.py`); the nightly
workflow (`.github/workflows/nightly.yml`) runs it on a freshly downloaded
corpus subset.

## Expectations & caveats

* **Version drift is a corpus property, not a bug.** The DSV2 solutions were
  written against an older Mathlib; under our pinned release a fraction fail
  to compile at all (259/438 clean on v4.31.0). The replayer records per-file
  outcomes; reports are over the replayable subset. The differential gate is
  immune to this: it compares stock vs fast on identical inputs, so a
  drifted file just fails on both sides.
* Instrumented rows: `ty:"oracle"` (the certificate problems),
  `ty:"tactic"` (per-invocation timing), `ty:"prep"`/`ty:"fast"`
  (preprocessing + fast-path telemetry).
* Report provenance: record Mathlib rev + farkas commit + source + file
  count next to any numbers you publish; that is the first thing to align
  when two machines disagree.
