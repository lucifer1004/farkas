/-
Instrumentation and activation layer for `linarith`/`nlinarith`.

Registers shadow tactic elaborators for the existing syntax kinds
`Mathlib.Tactic.linarith` and `Mathlib.Tactic.nlinarith` (elaborators
registered later are tried first — no Mathlib rebuild needed), reproducing
the stock v4.31.0 behavior verbatim except that:
  * the probe-then-restrict fast path runs first (on by default,
    `FARKAS_FAST=0` opts out),
  * the certificate oracle is wrapped with input serialization + timing,
  * the whole tactic invocation and each preprocessor are timed.

Telemetry rows (JSONL, see Farkas/Telemetry.lean): one per oracle call
("ty":"oracle"), one per tactic invocation ("ty":"tactic"), plus
"prep"/"fast" rows, correlated by "call". $FARKAS_SRC tags rows with the
source file being replayed. Timestamps are monotonic ns, comparable across
processes on one host (arrival-pattern data).
-/
import Mathlib.Tactic.Linarith.Frontend
import Farkas.Native
import Farkas.Fast

open Lean Elab Parser Tactic Meta Syntax

namespace Farkas
open Mathlib.Tactic
open Mathlib.Tactic.Linarith
open Farkas.Telemetry (jstr row emit compJson)

/-- Monotone id correlating the telemetry rows of one tactic invocation. -/
initialize seq : IO.Ref Nat ← IO.mkRef 0

private def certJson (m : Std.HashMap Nat Nat) : String :=
  let ps := m.fold (fun acc i c => s!"[{i},{c}]" :: acc) []
  s!"[{",".intercalate ps}]"

private def srcTag : IO String := return (← IO.getEnv "FARKAS_SRC").getD ""

/-- Wraps a `CertificateOracle`, logging inputs, timing, and outcome.
`id` is captured at invocation time: under parallel elaboration the global
counter may advance between the tactic start and the oracle call. -/
def loggingOracle (id : Nat) (inner : CertificateOracle) : CertificateOracle where
  produceCertificate hyps maxVar := do
    -- serialize BEFORE starting the clock so `ns` is pure oracle time
    let hypsJson := "[" ++ ",".intercalate (hyps.map compJson) ++ "]"
    let src ← srcTag
    let t0 ← IO.monoNanosNow
    let base : List (String × String) :=
      [("ty", jstr "oracle"), ("call", toString id), ("t", toString t0),
       ("src", jstr src), ("maxVar", toString maxVar),
       ("nHyps", toString hyps.length), ("hyps", hypsJson)]
    try
      let r ← inner.produceCertificate hyps maxVar
      let t1 ← IO.monoNanosNow
      emit <| row (base ++ [("ns", toString (t1 - t0)), ("ok", "true"), ("cert", certJson r)])
      return r
    catch e =>
      let t1 ← IO.monoNanosNow
      emit <| row (base ++ [("ns", toString (t1 - t0)), ("ok", "false"), ("cert", "null")])
      throw e

private def tacticRow (kind : String) (id t0 dur : Nat) (ok : Bool) : IO String := do
  return row [("ty", jstr "tactic"), ("kind", jstr kind), ("call", toString id),
              ("t", toString t0), ("src", jstr (← srcTag)),
              ("ns", toString dur), ("ok", toString ok)]

/-- Wrap a preprocessor with wall-clock logging (row ty:"prep"): input/output
hypothesis counts and duration, correlated to the tactic invocation by id. -/
private def timedPreprocessor (id : Nat) (pp : GlobalBranchingPreprocessor) :
    GlobalBranchingPreprocessor where
  name := pp.name
  description := pp.description
  transform g l := do
    let t0 ← IO.monoNanosNow
    try
      let r ← pp.transform g l
      let t1 ← IO.monoNanosNow
      emit <| row [("ty", jstr "prep"), ("call", toString id),
        ("name", jstr pp.name.toString), ("ns", toString (t1 - t0)),
        ("nIn", toString l.length),
        ("nOut", toString (r.foldl (fun a b => a + b.2.length) 0)),
        ("ok", "true")]
      return r
    catch e =>
      let t1 ← IO.monoNanosNow
      emit <| row [("ty", jstr "prep"), ("call", toString id),
        ("name", jstr pp.name.toString), ("ns", toString (t1 - t0)),
        ("nIn", toString l.length), ("nOut", "0"), ("ok", "false")]
      throw e

private def runInstrumented (kind : String) (onlyOn : Bool) (args : List Expr)
    (cfg : LinarithConfig) : TacticM Unit := do
  let id ← seq.modifyGet fun n => (n + 1, n + 1)
  -- FARKAS_ORACLE=native swaps the underlying oracle for the Rust daemon
  -- (A/B switch for end-to-end measurement); logging wraps either one.
  let baseOracle ← match (← IO.getEnv "FARKAS_ORACLE") with
    | some "native" => pure Farkas.native
    | _ => pure cfg.oracle
  -- telemetry wrappers only when a sink is configured: production users
  -- pay zero serialization cost
  let telemetryOn := (← IO.getEnv "FARKAS_CORPUS_FILE").isSome
  let cfg := if telemetryOn then
    { cfg with
      oracle := loggingOracle id baseOracle
      preprocessors := cfg.preprocessors.map (timedPreprocessor id) }
  else { cfg with oracle := baseOracle }
  let t0 ← IO.monoNanosNow
  -- Probe-then-restrict fast path: ON by default (degrades silently when no
  -- daemon binary is discoverable); FARKAS_FAST=0 opts out. Falls back to
  -- the stock path below on any failure. v2 covers `only` and `[args]` forms.
  if (← IO.getEnv "FARKAS_FAST") != some "0" then
    if ← Farkas.Fast.tryFast (kind == "nlinarith") onlyOn args cfg id then
      emit (← tacticRow kind id t0 ((← IO.monoNanosNow) - t0) true)
      return
  try
    commitIfNoEx do liftMetaFinishingTactic <| Linarith.linarith onlyOn args cfg
    emit (← tacticRow kind id t0 ((← IO.monoNanosNow) - t0) true)
  catch e =>
    emit (← tacticRow kind id t0 ((← IO.monoNanosNow) - t0) false)
    throw e

-- Shadow elaborators: bodies replicate Mathlib/Tactic/Linarith/Frontend.lean
-- (v4.31.0) exactly, with the oracle wrapped.

elab_rules : tactic
  | `(tactic| linarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) =>
    withMainContext do
      let args ← ((args.map (TSepArray.getElems)).getD {}).mapM
        (elabTermWithoutNewMVars `linarith)
      let cfg := (← Mathlib.Tactic.elabLinarithConfig cfg).updateReducibility bang.isSome
      runInstrumented "linarith" o.isSome args.toList cfg

elab_rules : tactic
  | `(tactic| nlinarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) =>
    withMainContext do
      let args ← ((args.map (TSepArray.getElems)).getD {}).mapM
        (elabTermWithoutNewMVars `nlinarith)
      let cfg := (← Mathlib.Tactic.elabLinarithConfig cfg).updateReducibility bang.isSome
      let cfg := { cfg with preprocessors := cfg.preprocessors.concat nlinarithExtras }
      runInstrumented "nlinarith" o.isSome args.toList cfg

end Farkas
