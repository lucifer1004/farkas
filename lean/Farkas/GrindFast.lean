/-
EXPERIMENTAL — probe-guided fact selection for `grind` (prototype).

Hypothesis under test (docs/grind.md): grind pays per hypothesis, so the
farkas numeric probe should be able to cut its cost by pre-selecting the
arithmetic facts, the way it selects hypotheses for linarith. Without a
fact-gating hook inside grind, the only tool available to a library is the
axe: `clear` the non-selected propositional hypotheses, run `grind`, and
fall back to a full-context `grind` on any failure.

Two tactics, both emitting `ty:"gf"` telemetry rows (nanosecond timing):

  `grind_timed`  — plain `grind`, timed: the baseline;
  `grind_fast`   — probe → tryClear non-selected prop hyps → `grind`,
                   with full-context fallback.

Not part of the supported surface; results feed the grind conversation.
-/
import Farkas.Fast

open Lean Elab Tactic Meta

namespace Farkas.GrindFast

open Farkas.Telemetry in
private def emitGf (fields : List (String × String)) : IO Unit :=
  Telemetry.emit <| row (("ty", jstr "gf") :: fields)

/-- Run `grind` on the current goals, timed. -/
private def runGrind : TacticM Nat := do
  let t0 ← IO.monoNanosNow
  evalTactic (← `(tactic| grind))
  return (← IO.monoNanosNow) - t0

/-- EXPERIMENTAL: plain `grind`, with per-call telemetry timing (baseline
for the fact-selection measurement). -/
syntax (name := grindTimed) "grind_timed" : tactic

elab_rules : tactic
  | `(tactic| grind_timed) => do
    let ns ← runGrind
    emitGf [("tac", "\"timed\""), ("outcome", "\"ok\""), ("ns", toString ns)]

/-- EXPERIMENTAL: probe-guided fact selection for `grind` — the numeric probe
selects the relevant arithmetic hypotheses, the rest are `tryClear`ed, and
`grind` runs on the slimmed context; any failure falls back to a
full-context `grind`. See docs/grind.md. -/
syntax (name := grindFastStx) "grind_fast" : tactic

elab_rules : tactic
  | `(tactic| grind_fast) => do
    let t0 ← IO.monoNanosNow
    let g ← getMainGoal
    let sel? ← tryCatch (Farkas.Fast.probeSelect false g) (fun _ => pure none)
    match sel? with
    | none =>
      let ns ← runGrind
      emitGf [("tac", "\"fast\""), ("outcome", "\"probe-miss\""),
              ("ns", toString ((← IO.monoNanosNow) - t0)), ("nsGrind", toString ns)]
    | some sel => do
      let selIds : Std.HashSet FVarId :=
        sel.filterMap (·.fvarId?) |>.foldl (init := {}) (·.insert ·)
      let s ← saveState
      try
        -- the axe: drop non-selected propositional hypotheses
        let lctx ← g.withContext getLCtx
        let mut cur := g
        let mut cleared := 0
        for decl in lctx do
          if decl.isImplementationDetail then continue
          if selIds.contains decl.fvarId then continue
          let isP ← cur.withContext do Meta.isProp decl.type
          if isP then
            let cur' ← cur.tryClear decl.fvarId
            if cur' != cur then cleared := cleared + 1
            cur := cur'
        replaceMainGoal [cur]
        let ns ← runGrind
        emitGf [("tac", "\"fast\""), ("outcome", "\"fast\""),
                ("ns", toString ((← IO.monoNanosNow) - t0)),
                ("nsGrind", toString ns), ("cleared", toString cleared),
                ("kept", toString selIds.size)]
      catch _ =>
        restoreState s
        let ns ← runGrind
        emitGf [("tac", "\"fast\""), ("outcome", "\"fallback\""),
                ("ns", toString ((← IO.monoNanosNow) - t0)), ("nsGrind", toString ns)]

end Farkas.GrindFast
