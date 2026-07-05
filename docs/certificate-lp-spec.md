# The exact certificate LP specification of Mathlib `linarith` (v4.31.0 sources)

All paths below are relative to
`lean/.lake/packages/mathlib/Mathlib/` in this repo. Corpus rows are the JSON
objects with `ty:"oracle"` in a replay run's `oracle.*.jsonl` files; each row
records the
exact `List Comp` handed to `CertificateOracle.produceCertificate` plus the
certificate Mathlib's simplex oracle returned.

Mechanical validation: `oracle/validate_spec.py` checks the interpretation in
this document against all 4548 known-good corpus certificates —
**4548/4548 (100.0000%) validate**, and the structural invariants of §1/§4 hold
on all 4599 oracle rows (0 exceptions).

---

## 1. `Comp` / `Linexp` representation, and how constants are encoded

### 1.1 Data types

- `Linexp := List (Nat × Int)` — sparse linear form, "list of pairs of variable
  indices and coefficients", keys unique and sorted in *decreasing* index order
  (`Tactic/Linarith/Datatypes.lean:44-52`).
- `Comp := { str : Ineq, coeffs : Linexp }` represents the comparison
  `coeffs.sum (fun ⟨k,v⟩ ↦ v * Var[k])  str  0`, i.e. **`t R 0` with the right
  side always literal zero** (`Datatypes.lean:122-135`).
- `Ineq` is the 3-element enum `eq | le | lt` (`Data/Ineq.lean:28-30`).
- A corpus hyp `[<str>, [[a,c],...]]` is exactly one `Comp`:
  `Σ c·x_a  <str>  0`.

### 1.2 Indices are *monomial* indices; index 0 is the constant `1`

`Datatypes.lean:125`: "Index 0 is reserved for constants, i.e. `coeffs.find 0`
is the coefficient of 1."

Why this holds mechanically: parsing (`Tactic/Linarith/Parsing.lean`) converts
each hypothesis `t R 0` to a `Sum : TreeMap Monom ℤ` and then interns each
distinct *monomial* (not atom) into a running index map, assigning
`n := map.size` on first encounter (`elimMonom`, `Parsing.lean:203-210`; used
by `toComp`, `Parsing.lean:219-225`). The constant is the empty monomial
(`Parsing.lean:73-74,119-121`). The index map is threaded through all
hypotheses in order (`toCompFold`, `Parsing.lean:231-237`), and
`proveFalseByLinarith` always **prepends a proof of `-1 < 0`** to the input
list before parsing (`Tactic/Linarith/Verification.lean:204-209`, proof built
at `Verification.lean:142-144`). Since `-1 < 0` is the first expression parsed
and contains only the constant monomial, the constant monomial is the first
monomial ever interned and gets index 0. (Note: raw `Expr` atoms are numbered
from 1 by `linearFormOfAtom`, `Parsing.lean:145-151`, but those are the
indices *inside* monomials; the `Linexp` keys seen by the oracle are the
monomial indices from `elimMonom`.)

Consequences visible in every corpus row (checked, 4599/4599):

- **`hyps[0]` is always `["lt",[[0,-1]]]`** — the injected `-1 < 0`
  (coefficient −1 on the constant monomial 0).
- `maxVar` = number of distinct monomials − 1 (`linearFormsAndMaxVar` returns
  `map.size - 1`, `Parsing.lean:246-251`), so atoms range over `0..maxVar`
  *including* the constant atom 0.

Also relevant: preprocessing (`Tactic/Linarith/Preprocessing.lean:384-386`,
`defaultPreprocessors = [filterComparisons, nnrealToReal, natToInt,
strengthenStrictInt, compWithZero, cancelDenoms]`) has already rewritten every
hypothesis and the negated goal into the form `t R 0` (`compWithZero`,
`Preprocessing.lean:189-203`), cast ℕ to ℤ (`natToInt`,
`Preprocessing.lean:122`), strengthened integer `a < b` to `a + 1 ≤ b`
(`strengthenStrictInt`, `Preprocessing.lean:175-179`),
and cleared denominators (`cancelDenoms`) — so all `Linexp` coefficients are
integers.

### 1.3 Three concrete corpus rows checked by hand

1. `oracle.test.aime_1983_p1.jsonl` call 1, cert `[[9,1],[5,1],[0,1]]`:
   h9 = `le [[1,1],[0,-1]]` (x₁ − 1 ≤ 0), h5 = `le [[1,-1],[0,2]]`
   (−x₁ + 2 ≤ 0), h0 = `lt [[0,-1]]` (−1 < 0). Sum with weights 1,1,1:
   atom 1: 1−1 = 0; atom 0: −1+2−1 = 0. Combined strength `lt` (h0 is strict).
   Reading atom 0 as the constant: (x−1) + (2−x) + (−1) = 0 with `<` ⇒ `0 < 0`. ✓
2. `oracle.test.aime_1983_p2.jsonl` call 1, cert `[[8,1],[3,1]]`:
   h8 = `lt [[2,1],[1,-1]]`, h3 = `le [[2,-1],[1,1]]`. Atom 2: 1−1 = 0,
   atom 1: −1+1 = 0; constant atom absent from both (coefficient 0). Strength
   `lt` from h8. ✓ (No constant involvement — a pure `x₂ < x₁`, `x₂ ≥ x₁`
   clash.)
3. `oracle.test.aime_1984_p7.jsonl` call 1, cert `[[15,1],[7,1],[0,1]]`:
   h15 = `le [[4,1],[0,-997]]` (x₄ − 997 ≤ 0), h7 = `eq [[4,-1],[0,998]]`
   (−x₄ + 998 = 0), h0 = `lt [[0,-1]]`. Atom 4: 1−1 = 0; atom 0:
   −997+998−1 = 0. Strength `lt`. Semantically: x₄ ≤ 997 and x₄ = 998 give
   `1 ≤ 0`; adding the injected `-1 < 0` cancels the constant and makes it
   strict. ✓ — this is exactly why the constant atom participates in the
   equality rows and why `-1 < 0` exists.

---

## 2. The precise certificate validity condition

The oracle contract (`CertificateOracle`, `Datatypes.lean:266-279`;
`proveFalseByLinarith` docstring, `Verification.lean:180-190`; module doc
`Frontend.lean:43-44`): the certificate is a map `m : hypIdx → ℕ` such that

1. **`∑ᵢ m(i) · tᵢ = 0` identically** — the weighted sum of the `Linexp`s
   cancels on *every* monomial index, **including the constant index 0**.
   Verified in reconstruction by proving `∑ m(i)·tᵢ = 0` with the discharger
   (`ring`) (`Verification.lean:244-246`).
2. **At least one `i` with `m(i) > 0` has `strᵢ = lt`.** The combined strength
   of the sum is computed by `Ineq.max` (`Data/Ineq.lean:34-43`):
   `lt` if any summand is `lt`, else `le` if any is `le`, else `eq`
   (`Comp.add`, `Datatypes.lean:156-157`; proof-side analogue `addIneq`,
   `Verification.lean:92-101`). Reconstruction builds `∑ m(i)·tᵢ R 0` with
   `mkLTZeroProof` (`Verification.lean:108-126`), rewrites by the `= 0` proof
   and closes with `Linarith.lt_irrefl : ¬ a < a`
   (`Verification.lean:248-254`, `Tactic/Linarith/Lemmas.lean:27`) — this
   **requires `R = lt`**; a combined `le` or `eq` would not produce `False`.

Both conditions together are exactly `Comp.isContr` of the weighted-sum `Comp`:
"no coefficients and strength `<`, i.e. `0 < 0`"
(`Datatypes.lean:167-171`).

Corner cases pinned down:

- **All-`le` cert summing to zero coefficients is NOT a contradiction**
  (combined strength `le` gives `0 ≤ 0`). Likewise **all-`eq`** gives `0 = 0`.
  `Comp.isContr` demands `str = lt`. The oracle can never emit such a cert
  anyway: its objective is the sum of strict-hyp coefficients and success
  requires it positive (§3).
- A "constant contradiction" like `1 ≤ 0` (nonempty coeffs `[(0,1)]`, strength
  `le`) is **not** `isContr` either. Mathlib reaches strictness/emptiness by
  adding the always-present hyp 0 (`-1 < 0`): in the corpus, 1906/4548 certs
  use hyp 0, and in 1805 of those hyp 0 is the *only* strict hyp used.
- **Coefficient 0**: `mkSingleCompZeroOf 0` would degrade a hyp to `eq`
  (`Datatypes.lean:301-307`), but the oracle post-processing filters zero
  entries out of the map (`Oracle/SimplexAlgorithm.lean:39-40`), so cert
  entries are always strictly positive naturals (checked: all 4548).
- **Equalities never need negative multipliers.** Before parsing,
  `proveFalseByLinarith` runs `addNegEqProofsIdx`
  (`Verification.lean:152-162`, called at `Verification.lean:205`): every
  proof of `t = 0` is accompanied by a proof of `-t = 0`. So the oracle's hyp
  list contains **both orientations of every equality as separate hyps**
  (checked: in all 4599 rows every `eq` hyp has its exact negation present),
  and nonnegative multipliers suffice. This is why corpus rows show `eq` hyps
  in ± pairs, e.g. `["eq",[[4,-1],[0,24]]],["eq",[[4,1],[0,-24]]]`.
- Hyp order in the corpus = oracle input order: index 0 is the injected
  `-1 < 0`, followed by the (preprocessed) hypotheses *reversed* relative to
  linarith's internal list, with each equality adjacent to its negation
  (`Verification.lean:204-209`: `(negOneProof, none) :: l'.reverse`).

---

## 3. The LP the `simplexAlgorithmSparse` oracle actually solves

Entry: `CertificateOracle.simplexAlgorithmSparse`
(`Tactic/Linarith/Oracle/SimplexAlgorithm.lean:47-51`).

### 3.1 Problem matrix (`preprocess`, `Oracle/SimplexAlgorithm.lean:25-31`)

From `hyps : List Comp` and `maxVar`, build
`A : (maxVar+1) × (hyps.length)` over ℚ with
`A[var, hypIdx] = coefficient of monomial var in hyp hypIdx`
(one **row per monomial, constant row 0 included**; one **column per hyp**),
and `strictIndexes := indexes of hyps with str = lt`.

Goal (`findPositiveVector`, `Oracle/SimplexAlgorithm/PositiveVector.lean:90-104`
and module doc `PositiveVector.lean:12-21`): find `v ≥ 0` with `A v = 0` and
`Σ_{i ∈ strictIndexes} v_i > 0` — i.e. a nonneg vector in the null space of A
whose strict-coordinate sum is positive ("positive vector" in the row
null-space formulation).

### 3.2 Homogenized tableau (`stateLP`, `PositiveVector.lean:44-75`)

With `n = maxVar+1`, `m = hyps.length`, build `B : (n+2) × (m+3)` with column
order `f, z, x₁..x_m, y` (`PositiveVector.lean:60-64` comment,
`:66-75` code):

- row 0 (objective): `-f + Σ_{i ∈ strictIndexes} x_i = 0`
  (`PositiveVector.lean:68-69`); `f` is the objective "sum of strict
  coefficients", to be made positive (`PositiveVector.lean:49-50`).
- row 1 (bounding): `z + Σᵢ xᵢ − y = 0` (`PositiveVector.lean:70-71`), where
  `y` is the "homogenized 1" and slack `z` bounds `Σ xᵢ ≤ y`
  (`PositiveVector.lean:52-55`).
- rows 2..n+1: `A` shifted by (+2,+2) (`PositiveVector.lean:73`), i.e.
  `A x = 0`.

### 3.3 Initial feasible point via Gauss (`Oracle/SimplexAlgorithm/Gauss.lean`)

`Gauss.getTableau B` (`Gauss.lean:35-84`) row-reduces `B x = 0`, splitting
variables into *basic* (pivot columns, collected greedily left→right,
`Gauss.lean:42-63`) and *free*, returning a `Tableau` in which each basic
variable is a linear combination of the free ones (signs negated at
`Gauss.lean:68-74`). The column placement makes `f` basic (leftmost) and `y`
free (rightmost); `z` sits between `f` and the `x`s so that the last tableau
column (the `y` column ≙ setting `y = 1`, all other free vars 0) is
nonnegative — a feasible starting vertex (`PositiveVector.lean:60-64`).

### 3.4 Simplex with Bland's rule (`Oracle/SimplexAlgorithm/SimplexAlgorithm.lean`)

`runSimplexAlgorithm` (`SimplexAlgorithm.lean:122-126`) pivots until
`checkSuccess` (`SimplexAlgorithm.lean:65-68`): objective value
`mat[0, last]` **> 0** and all basic values ≥ 0. Entering variable: smallest
original index among free variables with positive objective coefficient
(Bland's rule, `SimplexAlgorithm.lean:74-86,108-116`); if none exists the
problem is infeasible and the oracle throws (`SimplexAlgorithm.lean:83-85`,
surfaced as "linarith failed to find a contradiction",
`Verification.lean:218-223`). Exiting variable: tightest ratio bound, ties by
smallest index (`SimplexAlgorithm.lean:92-106`). Termination is guaranteed by
Bland's rule (`SimplexAlgorithm.lean:14-15`).

### 3.5 Extraction and scaling to ℕ

`extractSolution` (`PositiveVector.lean:77-82`) reads the basic-variable
values from the last tableau column (free vars, including `y`, contribute 0
except `y = 1` scaling), drops the auxiliary `f, z, y`, and returns
`v : Array ℚ` indexed by hyp. `postprocess`
(`Oracle/SimplexAlgorithm.lean:33-41`) multiplies by
`common_den = lcm of all denominators` and keeps nonzero entries:
`HashMap hypIdx ↦ ℕ` with strictly positive values. (Scaling by a positive
rational preserves both conditions of §2, and the corpus `cert` field is
exactly this map as a list.)

Latent quirk (verified benign, but relevant to reimplementers):
`extractSolution` writes `ans[basic[i] - 2]` with *Nat* subtraction
(`PositiveVector.lean:80-81`), so when `z` (column 1) is basic — which the
column placement guarantees — `z`'s value is first written to `ans[0]`, the
certificate slot of hyp 0. This is only overwritten (with the correct value)
if column 2 (hyp 0's variable `x₁`) is itself basic. That is in turn
guaranteed because hyp 0 is always the injected `-1 < 0`, whose −1 entry on
the atom-0 row (tableau row 2) makes column 2 the row-2 Gauss pivot. An
implementation that drops the `-1 < 0` injection could hit this aliasing and
emit a spurious coefficient on hyp 0.

---

## 4. Reduction for external solvers: the certificate-space feasibility LP

Given one corpus row with `K = nHyps` hyps `(strᵢ, Lᵢ)` (each `Lᵢ` a sparse
map atom→int) and `V = maxVar + 1` atoms (atom 0 = constant), build:

- **Variables** `λ ∈ ℚ^K`, `λᵢ ≥ 0` for **all** i (equalities included — no
  free/negative multipliers are ever needed because both orientations of every
  equality are already present as separate hyps, §2; checked on all 4599 rows).
- **Equality rows** (matrix `A ∈ ℚ^{V×K}`, `A[a,i] = Lᵢ[a]` or 0): one row per
  atom `a = 0,1,...,maxVar`, **constant atom 0 included**:
  `Σᵢ A[a,i] · λᵢ = 0`  (sense `=`, rhs `b = 0`).
- **Strictness row**: let `S = { i : strᵢ = "lt" }` (nonempty in every corpus
  row since hyp 0 is `-1 < 0`). The homogeneous condition "`Σ_{i∈S} λᵢ > 0`"
  is not directly expressible; since the system is homogeneous (any positive
  scaling of a solution is a solution), normalize it to
  `Σ_{i∈S} λᵢ ≥ 1`  (sense `≥`, rhs 1).
  This is exactly Mathlib's objective `f > 0` (§3.2/§3.4) up to scaling.
- **Objective**: none needed (pure feasibility). `min Σᵢ λᵢ` or
  `min Σ_{i∈S} λᵢ` are fine choices for nicer certificates.

Feasible ⇔ a Mathlib-valid certificate exists; infeasible ⇔ the oracle
(correctly) fails. From a rational feasible point, recover the Nat certificate
exactly as Mathlib does: multiply by the lcm of denominators and drop zeros
(`Oracle/SimplexAlgorithm.lean:36-41`). The resulting map must then satisfy
§2's two checks (identically-zero weighted sum over all atoms incl. atom 0;
at least one `lt` hyp with positive weight).

Notes for the implementer:

- Do **not** special-case the constant: it is atom 0 and its row is an
  ordinary `= 0` row. "Constant" contradictions are absorbed by hyp 0
  (`-1 < 0`), which doubles as the universal strictness supplier.
- `eq` hyps get plain `λ ≥ 0` like everything else; they never appear in `S`.
- Strict-vs-nonstrict is enforced *only* by the single normalization row over
  `S`; `le`/`eq` hyps impose nothing beyond `λ ≥ 0` and the atom rows.
- All data is integral; exact rational LP (or integral scaling) avoids
  floating-point acceptance of near-solutions. A float solve must be followed
  by rationalization + the exact §2 check.
- **Float solvers also produce false INFEASIBLE verdicts on this corpus, not
  just false accepts.** Hyp coefficients reach ≈3.2·10²⁹
  (`oracle.test.amc12a_2008_p25.jsonl` line 20 — double-precision HiGHS
  reports its LP infeasible even though Mathlib's cert `[[19,1],[16,1]]` is
  an exact feasible point) and ≈1.4·10⁶⁰⁶
  (`oracle.test.amc12a_2013_p4.jsonl` line 1, whose cert *weight* is that
  same 607-digit natural). Matching Mathlib's feasible/infeasible answer on
  all rows requires exact rational arithmetic end to end.

## 5. Worked example

Real corpus row (replay corpus, `oracle.test.aime_1984_p7.jsonl` line 1,
abridged to the fields that matter; `maxVar = 8`, `nHyps = 16`):

```json
{"ty":"oracle","call":1,"src":"test/aime_1984_p7.lean","maxVar":8,"nHyps":16,
 "hyps":[["lt",[[0,-1]]],
         ["eq",[[1,-1],[0,1001]]],["eq",[[1,1],[0,-1001]]],
         ["eq",[[2,-1],[0,1000]]],["eq",[[2,1],[0,-1000]]],
         ["eq",[[3,-1],[0,999]]], ["eq",[[3,1],[0,-999]]],
         ["eq",[[4,-1],[0,998]]], ["eq",[[4,1],[0,-998]]],
         ["eq",[[5,-1],[0,997]]], ["eq",[[5,1],[0,-997]]],
         ["eq",[[7,-1],[6,1]]],   ["eq",[[7,1],[6,-1]]],
         ["eq",[[8,-1],[1,1]]],   ["eq",[[8,1],[1,-1]]],
         ["le",[[4,1],[0,-997]]]],
 "ok":true,"cert":[[15,1],[7,1],[0,1]]}
```

Reading (atom 0 = constant 1): hyp 0 is the injected `-1 < 0`; hyps 7/8 are
the ± pair for `x₄ = 998`; hyp 15 is the negated goal `x₄ − 997 ≤ 0`.

LP per §4: variables `λ₀..λ₁₅ ≥ 0`; 9 equality rows (atoms 0..8); strict set
`S = {0}` so strictness row `λ₀ ≥ 1`. Nonzero columns of `A`:

| atom | contribution `= 0` |
|------|--------------------|
| 0 | `−λ₀ +1001λ₁ −1001λ₂ +1000λ₃ −1000λ₄ +999λ₅ −999λ₆ +998λ₇ −998λ₈ +997λ₉ −997λ₁₀ −997λ₁₅ = 0` |
| 1 | `−λ₁ + λ₂ + λ₁₃ − λ₁₄ = 0` |
| 2 | `−λ₃ + λ₄ = 0` |
| 3 | `−λ₅ + λ₆ = 0` |
| 4 | `−λ₇ + λ₈ + λ₁₅ = 0` |
| 5 | `−λ₉ + λ₁₀ = 0` |
| 6 | `λ₁₁ − λ₁₂ = 0` |
| 7 | `−λ₁₁ + λ₁₂ = 0` |
| 8 | `−λ₁₃ + λ₁₄ = 0` |

Mathlib's certificate `[[15,1],[7,1],[0,1]]` is the point
`λ₀ = λ₇ = λ₁₅ = 1`, rest 0. Check: atom 0 row: `−1 + 998 − 997 = 0` ✓;
atom 4 row: `−1 + 1 = 0` ✓; other rows all-zero ✓; strictness `λ₀ = 1 ≥ 1` ✓.
Already integral, so the Nat cert is the same. Semantics:
`1·(x₄−997 ≤ 0) + 1·(998−x₄ = 0) + 1·(−1 < 0)` sums to `0 < 0`.

---

## 6. Mechanical validation results

`oracle/validate_spec.py --corpus <run>` implements §2 verbatim (weighted
sum zero on every atom incl. atom 0; ≥1 strict hyp with positive
coefficient; coefficients positive Nats) over every oracle row of a replay
run:

```
oracle rows:                 4599
rows with certificate:       4548
certificates valid:          4548
validation rate:             100.0000%

structural invariants:
  rows whose hyps[0] != ('lt', [[0,-1]]):    0
  rows with an eq hyp lacking its negation:  0
  valid certs using hyp 0 (-1 < 0):          1906
  valid certs whose only lt-hyp is hyp 0:    1805
```

No failing rows. Alternative interpretations are excluded as follows:

- **Requiring `str = lt` on *all* used hyps** (rather than `Ineq.max = lt`)
  is excluded by the positive rows: only 162/4548 certs would validate; the
  other 4386 mix `le`/`eq` hyps with a single strict one.
- **Excluding atom 0 from the cancellation** is a strictly *weaker* validity
  predicate, so the positive rows cannot discriminate it (all 4548 certs
  trivially still pass — every satisfied `= 0` row stays satisfied when the
  requirement is dropped). It is excluded by (a) the source: `preprocess`
  builds `A` with `maxVar+1` rows including monomial 0
  (`Oracle/SimplexAlgorithm.lean:25-31`), and the `ring` discharge must prove
  the full weighted sum — constants included — equal to 0
  (`Verification.lean:246`); and (b) the 51 corpus rows where Mathlib's exact
  oracle found *no* certificate (`cert:null`): dropping the atom-0 row makes
  **all 51** of them feasible (exact-rational-verified). Concretely, without
  the atom-0 row, `λ₀ = 1` (hyp 0, `-1 < 0`, by itself) is a "certificate"
  for *every* input — e.g. `oracle.valid.aimeI_2000_p7.jsonl` call 2, whose
  hyps `{-1<0, -x₁<0, -x₂<0, …}` are perfectly satisfiable, would be
  "refuted" by hyp 0 alone with atom-0 residual −1.
