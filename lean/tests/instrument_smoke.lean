/- Instrumentation smoke test. Compile with:
     FARKAS_CORPUS_FILE=/tmp/farkas_smoke.jsonl FARKAS_SRC=smoke \
       lake env lean tests/instrument_smoke.lean
   Expect: 4 tactic rows (3 ok, 1 failed) + oracle rows in the JSONL. -/
import Mathlib
import Farkas.Instrument

-- the failing example intentionally carries an unused hypothesis
set_option linter.unusedVariables false

example (x y : ℚ) (h1 : x < 1) (h2 : y ≤ 2) : x + y < 4 := by linarith

example (x : ℤ) (h : x ≥ 2) : x ≥ 1 := by linarith

example (a b : ℝ) (h : a ≤ b) (h2 : 0 ≤ b) : a * 0 ≤ b := by nlinarith

-- failing call (satisfiable hypotheses): exercises the ok:false path
example (x : ℚ) (h : x ≥ 0) : True := by
  fail_if_success linarith
  trivial
