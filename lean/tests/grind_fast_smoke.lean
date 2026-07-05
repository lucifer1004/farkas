/- Smoke test for the experimental grind fact-selection prototype.
   Compile with:  lake env lean tests/grind_fast_smoke.lean
   Must succeed with a daemon (probe active) and without (probe-miss →
   plain grind). -/
import Mathlib
import Farkas.GrindFast

set_option linter.unusedVariables false

-- probe hit: junk hypotheses get cleared before grind
example (x y : ℚ) (h1 : x < 3) (j1 : (5:ℚ) < 6) (j2 : (7:ℚ) ≤ 8)
    (h2 : y ≤ 2) : x + y < 6 := by grind_fast

-- ℤ with dependency structure
example (a b : ℤ) (h : a + 1 ≤ b) (j : (0:ℤ) ≤ 3) : a < b := by grind_fast

-- unparseable goal for the probe: must fall through to plain grind
example (p : Prop) (hp : p) : p := by grind_fast

-- baseline tactic also compiles
example (x : ℚ) (h : x < 1) : x < 2 := by grind_timed
