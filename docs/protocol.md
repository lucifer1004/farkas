# farkas daemon protocol

**Version: 1** (this document is normative for `farkas-oracled` and the Lean
client in `Farkas/Native.lean`).

The protocol is tactic-agnostic: requests are certificate-space LP
problems (docs/certificate-lp-spec.md), not "linarith problems" — any
client producing that shape (a future grind hook, another proof assistant)
is served identically.

Transport: line-oriented JSON over the daemon's stdin/stdout. One JSON object
per line in each direction; the daemon flushes after every response. Requests
are answered strictly in order. Blank lines are ignored.

## Handshake (optional but recommended)

The client MAY send, at any point:

```json
{"hello": true}
```

The daemon replies:

```json
{"farkas_protocol": 1, "version": "<crate version>", "engine": "tiered"}
```

Clients SHOULD verify `farkas_protocol == 1` on first connect and fail soft
(degrade to stock behavior) on mismatch. The reference Lean client does
this on every spawn, and serializes all round-trips behind a mutex —
responses are matched to requests by order, so concurrent unlocked writers
would corrupt the stream.

## Certificate request

```json
{"maxVar": M, "hyps": [[REL, [[atomIdx, intCoeff], ...]], ...]}
```

* `REL` ∈ `"lt" | "le" | "eq"` — the comparison `t REL 0`.
* Atom index `0` is the constant term (Mathlib linarith convention; see
  `docs/certificate-lp-spec.md`).
* `intCoeff` may be arbitrarily large (hundreds of digits); it is transmitted
  as a JSON number and parsed with arbitrary precision.
* Equality hypotheses MUST be present in **both orientations** (each
  `eq` row accompanied by its negation), exactly as Mathlib's
  `addNegEqProofs` produces them — certificate coefficients are
  nonnegative, so the daemon cannot use an equality "backwards" unless
  the mirrored row is present. The daemon does NOT mirror internally
  (an internal mirror could return certificate indices the client never
  sent). Single-orientation requests are answered soundly but may
  miss certificates.

## Responses

```json
{"cert": [[hypIdx, "natCoeff"], ...]}
```
A certificate: nonnegative integer coefficients per hypothesis index such
that the weighted sum of the hypotheses is a contradiction. **Coefficients
are JSON strings** — they can exceed any fixed-width integer. Every reported
certificate has already passed the daemon's exact BigRational verifier.

```json
{"cert": null}
```
Exact answer: no certificate exists. This only ever comes from the exact
tiered engine (never from floating-point evidence).

```json
{"error": "..."}
```
Malformed request or (never expected) internal error. The daemon stays alive
after errors; clients SHOULD treat an `error` response as a per-call miss and
fall back to stock behavior.

## Robustness guarantees

Fuzz-tested invariants (`oracle/native/tests/daemon_fuzz.rs`): every input
line — including random bytes, malformed JSON, wrong shapes, and
megabyte-scale garbage — gets exactly one JSON response line, and the daemon
keeps serving afterwards. The request parse path is panic-free by
construction, with a `catch_unwind` backstop in the serve loop (a per-request
panic answers `{"error":"internal panic"}` instead of dying, which would put
the client into a respawn loop). Requests with `maxVar > 1_000_000` are
rejected as `{"error":"maxVar too large"}` — the engines allocate `O(maxVar)`
tableau rows, so an absurd value from a corrupt client would otherwise be an
OOM. Giant-but-wellformed coefficients (tens of thousands of digits) are
answered exactly, merely slowly.

## Lifecycle

The daemon exits on stdin EOF. It performs no filesystem or network access.
Clients own restart policy (the reference Lean client retries a failed
round-trip once, respawning the daemon).
