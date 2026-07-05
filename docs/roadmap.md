# Roadmap

Where the project is and where it is heading.

## Done

Distribution (release matrix + `farkas-fetch`, protocol v1), correctness
hardening (property tests, protocol fuzz, differential gate in CI, drift
alarm), and fast-path coverage of all `linarith` forms — results and
caveats consolidated in `docs/evaluation.md`.

## Next

- **Launch**: first GitHub release (`v4.31.0-farkas.1`), Reservoir
  registration, Zulip announcement with the reproducible harness.
- **Upstream track 1 — opt-in package** (this repo): the supported
  consumption mode today (`import Farkas` / `import Farkas.Auto`).
- **Upstream track 2 — Mathlib PRs**: propose `set_option linarith.oracle`
  (the `CertificateOracle` interface is designed for pluggability; an
  option-based default would remove the shadow-elaborator layer, our main
  maintenance surface); later, a `preFilter` hook in `LinarithConfig` for
  native probe-then-restrict integration.
- **Upstream track 3 — LP-tooling convergence**: offer the tiered exact
  engine as a backend to the emerging `leanprover/lp` family; share the
  heavy-tail benchmark data (600-digit certificate coefficients) that
  stresses denominator-budget designs.

## Standing watches

- Mathlib linarith sources drift (alarm in CI; re-sync procedure in
  `docs/release.md`).
- Lean core `grind`'s linear-arithmetic solver as a long-term successor to
  linarith: measured stance and transfer analysis in `docs/grind.md`;
  `farkas-corpus.py grind-check` re-measures the takeover rate quarterly.
