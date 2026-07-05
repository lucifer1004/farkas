# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Repository tags follow the `v<mathlib release>-farkas.<n>` scheme described in
[docs/release.md](docs/release.md); the Rust crate (`farkas-core`) carries its
own semantic version, noted per entry.

## [Unreleased]

## [v4.31.0-farkas.1] - 2026-07-04

First public release. `farkas-core` 0.1.0.

### Added

- **Native certificate oracle** — `farkas-oracled`, a local Rust daemon that
  reimplements linarith's simplex certificate search behind Mathlib's
  pluggable `CertificateOracle` interface. Exact tiered-rational arithmetic
  (i64 → i128 → BigInt with checked promotion); JSON-lines protocol v1 over
  stdin/stdout, no network.
- **Probe-then-restrict fast path** — parse hypotheses numerically (no proof
  terms), ask the oracle which hypotheses the certificate uses, then run stock
  `linarith only [...]` on just those. Selection-only by construction: every
  proof is still built by stock linarith and checked by the kernel; any
  failure falls back to stock behavior.
- **Distribution** — `lake exe farkas-fetch` downloads the host-platform
  binary from the GitHub Release, verifies it against `SHA256SUMS`, and
  installs it under `.lake/farkas/`. Five prebuilt targets (Linux
  x86_64/aarch64 musl-static, macOS x86_64/aarch64, Windows x86_64 MSVC).
- **Measurement harness** — corpus acquire/replay/diff tooling
  (`scripts/farkas-corpus.py`), differential gate against Mathlib's linarith
  test suite, stress and fuzz suites. Setup, results, and threats to validity
  in [docs/evaluation.md](docs/evaluation.md).
- **Oracle contract spec** — [docs/certificate-lp-spec.md](docs/certificate-lp-spec.md),
  the exact semantics of linarith's `CertificateOracle` contract, mechanically
  validated against 4,548 certificates.
