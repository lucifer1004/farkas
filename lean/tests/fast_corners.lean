/- Fast-path corner cases: each example targets a probe
   semantics we got wrong (or nearly wrong) while replicating stock linarith's
   preprocessing — kept as compile gates so a re-sync can't silently regress
   them. Compile with:  lake env lean tests/fast_corners.lean
   Must succeed both with a daemon (fast path active) and without (stock
   degradation). `FARKAS_FAST_DEBUG=1` prints any probe miss.  -/
import Mathlib
import Farkas.Auto

-- several examples deliberately carry unused/contradictory hypotheses
set_option linter.unusedVariables false

-- eq mirroring: the certificate needs the *negated* orientation of h
-- (the missing-`addNegEqProofs` bug that pinned the hit rate at 33%)
example (x y : ℚ) (h : x = y) (h2 : y < 0) : x < 0 := by linarith
example (x y z : ℤ) (h : x + y = z) (h2 : z ≤ 0) (h3 : y ≥ 1) : x ≤ -1 := by
  linarith

-- ℕ strictness shift: `a < b` over ℕ must become `a + 1 ≤ b` (int-like shift)
example (a b : ℕ) (h : a < b) : a + 1 ≤ b := by linarith
example (n : ℕ) (h : 2 * n < 5) : n ≤ 2 := by linarith

-- casts as atoms: ↑a/↑b must intern consistently across hyps and goal.
-- (Stock linarith does NOT distribute ↑(a+b) — verified here 2026-07-03 —
-- so the probe's cast distribution can only ever *add* probe hits; the
-- ℕ-subtraction natSrc blocking is soundness-by-construction: a wrong
-- selection just falls back to stock. Both are covered by the differential
-- gate rather than by a compile assertion.)
example (a b : ℕ) (h : (a : ℚ) + b < 3) (h2 : (a : ℚ) ≥ 1) : (b : ℚ) < 2 := by
  linarith
example (a : ℕ) (h : (a : ℝ) * 2 ≤ 4) : (a : ℝ) ≤ 2 := by linarith

-- conjunction splitting: hypotheses arriving as ∧ bundles
example (x y : ℚ) (h : x < 1 ∧ y ≤ 2) : x + y < 4 := by linarith
example (x y z : ℝ) (h : x ≤ y ∧ y ≤ z ∧ 0 < 1) (h2 : z < 0) : x < 0 := by
  linarith

-- rational literals with denominators (lcm clearing in toComp)
example (x : ℚ) (h : x < 1/2) : 2 * x < 1 := by linarith
example (x : ℝ) (h : (0.25 : ℝ) ≤ x) : 1 ≤ 8 * x := by linarith

-- strict-from-products strength rule (nlinarith pool: lt·lt → lt)
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by nlinarith

-- v2: explicit arg terms — context + args pool
example (x y : ℚ) (h1 : x < 1) (h2 : y < 3) : x + y < 4 := by
  linarith [h2.le]   -- arg term mixed with context h1
example (u v : ℝ) (h : u ≤ v) (hv : v ≤ 0) : u * 1 ≤ 0 := by
  linarith [mul_one u]

-- v2: only-mode — the context is excluded, exactly like stock
example (x y : ℚ) (h1 : x < 1) (h2 : y ≤ 2) (junk : x > 5) : True := by
  fail_if_success linarith only [h1]   -- h1 alone can't close x + y < 4… or anything
  trivial
example (x y : ℚ) (h1 : x < 1) (h2 : y ≤ 2) : x + y < 4 := by
  linarith only [h1, h2]
-- only-mode must NOT see contradictory context it wasn't given
example (x : ℚ) (hx : x < 0) (hx' : x > 1) : x < 1 := by
  linarith only [hx]

-- v2: nlinarith with args
example (a b : ℝ) (ha : 0 ≤ a) : 0 ≤ a * a + b * b := by
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a+b)]

-- fallback correctness: goals the probe may miss must still close via stock
example (x : ℚ) (h : |x| ≤ 1) : x ≤ 1 := by
  cases abs_le.mp h with
  | intro _ hr => linarith

-- and a genuinely-satisfiable context must still fail cleanly
example (x : ℚ) (h : x ≥ 0) : True := by
  fail_if_success linarith
  trivial
