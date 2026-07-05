import Farkas.Instrument

/-!
# `Farkas.Auto` — drop-in acceleration for `linarith`/`nlinarith`

Importing this module (or the package root `Farkas`) registers shadow
elaborators for the existing `linarith`/`nlinarith` syntax, so **no proof
scripts change**. Behavior:

* If the `farkas-oracled` daemon binary is discoverable
  (`Farkas.findBinary`: env override → artifact slot → PATH), calls go
  through the probe-then-restrict fast path with the native exact oracle,
  falling back to stock on any failure.
* If no binary is found, behavior is exactly stock `linarith` plus a
  one-time note. **A missing binary never breaks a build.**
* `FARKAS_FAST=0` opts out of the fast path entirely.
* Telemetry is inert unless `FARKAS_CORPUS_FILE` is set
  (see `Farkas.Instrument`).

Soundness: the fast path only *selects hypotheses*; every proof is still
constructed by stock linarith and checked by the kernel.
-/
