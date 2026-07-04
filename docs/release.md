# Versioning & release process

## Tag scheme

`v<mathlib release>-farkas.<n>` — e.g. `v4.31.0-farkas.1`, `v4.31.0-farkas.2`,
`v4.32.0-farkas.1`.

The Mathlib segment is a real compatibility claim, not decoration: the fast
path mirrors stock linarith's preprocessing semantics and `Instrument.lean`
carries copies of the two elab bodies, so a farkas build is only vouched for
against the Mathlib release it was synced to (enforced by
`scripts/check-mathlib-drift.sh`). `<n>` counts farkas iterations within one
Mathlib release. `main` tracks the latest supported Mathlib stable.

## Cutting a release

1. CI green on `main` (includes the drift alarm and the musl check).
2. Bump `Farkas.Fetch.defaultTag` in `lean/Farkas/Fetch.lean` to the new tag.
3. `git tag v<mathlib>-farkas.<n> && git push --tags`.
4. `release.yml` builds `farkas-oracled` for the five targets and attaches
   tarballs + `SHA256SUMS` to the GitHub Release:

   | target | linkage |
   |---|---|
   | x86_64-unknown-linux-musl | static (musl) |
   | aarch64-unknown-linux-musl | static (musl) |
   | aarch64-apple-darwin | system libs only |
   | x86_64-apple-darwin | system libs only |
   | x86_64-pc-windows-msvc | static CRT |

   All binaries use mimalloc as the global allocator (musl's malloc degrades
   under the BigRational tail + rayon batch mode).
5. Sanity on a clean checkout: `lake exe farkas-fetch` then the smoke test.

`lake exe farkas-fetch` downloads the artifact for the host platform,
verifies it against `SHA256SUMS`, unpacks into `.lake/farkas/`, and asks the
binary for `--version`. Unsupported platforms get a cargo-build fallback
message; a missing binary never breaks a build (stock linarith + one-time
note).

## Syncing to a new Mathlib release

1. Bump `rev` in `lean/lakefile.toml` and `lean/lean-toolchain`; `lake update`.
2. If `scripts/check-mathlib-drift.sh` fails: diff the watched linarith
   sources, re-sync `Farkas/{Instrument,Fast}.lean`, re-run the differential
   replay (outcomes must be bit-identical vs stock), then
   `scripts/check-mathlib-drift.sh --update`.
3. Tag `v<new mathlib>-farkas.1`.

## Reservoir

Reservoir (the Lean package index) indexes public GitHub repos with a
build-passing lakefile once registered. NOTE: the Lean package manifest
lives in `lean/`, not the repository root — verify Reservoir's
subdirectory support at registration time; if it requires a root
lakefile, promoting `lean/` to the root is the fallback (consumers use
`subDir = "lean"` either way until then). After the first release:
register, confirm the index entry, add the badge to the README.
