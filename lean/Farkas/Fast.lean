/-
Probe-then-restrict fast path for `linarith`/`nlinarith`.

Instead of running the stock pipeline (preprocessing + ring-normalizing parse,
both O(n) in hypotheses and O(n^2) for nlinarith products, all building proof
terms eagerly), we:

  1. PROBE: parse the hypothesis pool + negated goal into sparse linear
     forms *numerically* — no proof terms, no `mkAppM`, no ring normalization.
     The pool is the local context plus explicit `[args]` terms, or the args
     alone under `only` — exactly stock's pool per form. Numeric equivalents
     of the stock preprocessing semantics are applied:
       * splitConjunctions (∧ hyps split, `collectHyp`);
       * removeNegations (¬(a<b) ⇒ b≤a, ¬(a≤b) ⇒ b<a; ¬(a=b) dropped);
       * cancelDenoms (denominator lcm cleared, `toComp`);
       * strengthenStrictInt (t < 0 ⇒ t+1 ≤ 0 over ℤ/ℕ);
       * natToInt nonnegativity facts for ℕ-typed atoms;
       * eq mirroring (both orientations, like `addNegEqProofs`) and the
         `-1 < 0` seed as hyp 0, in `runProbe`;
       * ring-normalization atom matching: casts distribute (ℕ-sub blocked),
         `a / b` ≡ `a·b⁻¹` with `x⁻¹` unification, `^2`/`^1`/`^0` expanded;
       * for nlinarith: square facts and pairwise products over the pool
         (monomials become synthetic atoms).
     There is no type whitelist: atoms are opaque, so any ordered structure
     probes; ℕ/ℤ get the semantics above via `isIntLike`/`natTyped`.
     NOT mirrored: `nnrealToReal` (ℝ≥0 hyps probe with field-like semantics
     and may mis-select — a measured residual, see docs/evaluation.md §4).
  2. Ask the native oracle for a certificate over these forms.
  3. RESTRICT: map the certificate's hypotheses back to their parents S
     (context fvars and/or arg terms; a product maps to both factors) and
     run the *stock* `Linarith.linarith true S cfg` — full
     preprocessing/parse/reconstruction, but on |S| ≈ 5 hypotheses.
  4. Any failure anywhere → silent fallback to the stock full run.
     (`FARKAS_FAST_DEBUG=1` emits per-miss telemetry incl. probe comps.)

Soundness is untouched: the fast path only ever *selects hypotheses*; every
proof step is still produced and checked by the stock machinery.
-/
import Mathlib.Tactic.Linarith.Frontend
import Farkas.Native

open Lean Meta Elab Tactic
open Mathlib.Tactic.Linarith

namespace Farkas.Fast

/-- Sparse polynomial over probe atoms: atom id → coefficient.
Key 0 is the constant term; base and monomial atoms get ids ≥ 1. -/
abbrev Poly := Std.HashMap Nat Rat

/-- Interning state threaded through one probe: every distinct atom
(base expr, degree-2 pair, degree-≥3 monomial) gets a stable id. -/
structure ParseState where
  /-- structural-equality interning of base atom exprs -/
  baseIds : Std.HashMap Expr Nat := {}
  /-- degree-2 monomials keyed by ordered base-id pair -/
  pairIds : Std.HashMap (Nat × Nat) Nat := {}
  /-- degree-≥3 monomials keyed by sorted base-id list -/
  junkIds : Std.HashMap (List Nat) Nat := {}
  /-- next unassigned atom id (0 is the constant) -/
  nextId : Nat := 1
  /-- pair-atom id ↦ its (i,j); needed for square-fact generation -/
  pairs : List (Nat × Nat × Nat) := []

/-- Pure parsing monad over the shared `ParseState`. -/
abbrev ParseM := StateM ParseState

private def internBase (e : Expr) : ParseM Nat := do
  let s ← get
  match s.baseIds[e]? with
  | some i => return i
  | none =>
    let i := s.nextId
    set { s with baseIds := s.baseIds.insert e i, nextId := i + 1 }
    return i

private def internPair (a b : Nat) : ParseM Nat := do
  let key := (min a b, max a b)
  let s ← get
  match s.pairIds[key]? with
  | some i => return i
  | none =>
    let i := s.nextId
    set { s with pairIds := s.pairIds.insert key i, nextId := i + 1,
                 pairs := (i, key.1, key.2) :: s.pairs }
    return i

private def internJunk (ids : List Nat) : ParseM Nat := do
  let key := ids.mergeSort (· ≤ ·)
  let s ← get
  match s.junkIds[key]? with
  | some i => return i
  | none =>
    let i := s.nextId
    set { s with junkIds := s.junkIds.insert key i, nextId := i + 1 }
    return i

private def pconst (c : Rat) : Poly := if c == 0 then {} else ({} : Poly).insert 0 c
private def padd (p q : Poly) : Poly := q.fold (fun r k v =>
  let v' := r.getD k 0 + v
  if v' == 0 then r.erase k else r.insert k v') p
private def pscale (c : Rat) (p : Poly) : Poly :=
  if c == 0 then {} else p.fold (fun r k v => r.insert k (c * v)) {}

/-- Which base ids make up an atom id (for monomial multiplication). -/
private def atomFactors (s : ParseState) (i : Nat) : List Nat :=
  match s.pairs.find? (fun (p, _, _) => p == i) with
  | some (_, a, b) => [a, b]
  | none =>
    match s.junkIds.fold (fun acc k v => if v == i then some k else acc) none with
    | some k => k
    | none => [i]

/-- Multiply two polynomials, interning product monomials as synthetic atoms. -/
private def pmul (p q : Poly) : ParseM Poly := do
  let mut r : Poly := {}
  for (ka, va) in p.toList do
    for (kb, vb) in q.toList do
      let coeff := va * vb
      let key ← do
        if ka == 0 then pure kb
        else if kb == 0 then pure ka
        else
          let s ← get
          let fac := atomFactors s ka ++ atomFactors s kb
          if fac.length == 2 then internPair fac[0]! fac[1]!
          else internJunk fac
      let v' := r.getD key 0 + coeff
      r := if v' == 0 then r.erase key else r.insert key v'
  return r

/-- Scientific literal (`0.5` elaborates to `OfScientific.ofScientific`). -/
private def scientific? (e : Expr) : Option Rat :=
  match e.getAppFnArgs with
  | (``OfScientific.ofScientific, #[_, _, m, b, x]) => do
    let m ← m.nat?
    let x ← x.nat?
    let isNeg := b.isConstOf ``Bool.true
    if isNeg then pure (mkRat m (10 ^ x)) else pure ((m * 10 ^ x : Int) : Rat)
  | _ => none

private def isCastHead (n : Name) : Bool :=
  n == ``Nat.cast || n == ``Int.cast || n == ``Rat.cast ||
  n == ``NatCast.natCast || n == ``IntCast.intCast || n == ``RatCast.ratCast

/-- Distribute a cast homomorphically over +, *, ^, literals (mirrors
`push_cast` in the stock `natToInt`). `castOf` rebuilds the cast around a
leaf so atoms stay well-typed; `natSrc` blocks distribution over ℕ
subtraction/division/negation, which are not homomorphic. -/
private partial def parseCastForm (castOf : Expr → Expr) (natSrc : Bool) (e : Expr) :
    ParseM Poly := do
  if let some q := e.rat? then return pconst q
  if let some q := scientific? e then return pconst q
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return padd (← parseCastForm castOf natSrc a) (← parseCastForm castOf natSrc b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      if natSrc then return ({} : Poly).insert (← internBase (castOf e)) 1
      else return padd (← parseCastForm castOf natSrc a)
                       (pscale (-1) (← parseCastForm castOf natSrc b))
  | (``Neg.neg, #[_, _, a]) =>
      if natSrc then return ({} : Poly).insert (← internBase (castOf e)) 1
      else return pscale (-1) (← parseCastForm castOf natSrc a)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      pmul (← parseCastForm castOf natSrc a) (← parseCastForm castOf natSrc b)
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
      match n.rat? with
      | some q =>
        if q == 2 then do let p ← parseCastForm castOf natSrc a; pmul p p
        else if q == 1 then parseCastForm castOf natSrc a
        else if q == 0 then return pconst 1
        else return ({} : Poly).insert (← internBase (castOf e)) 1
      | none => return ({} : Poly).insert (← internBase (castOf e)) 1
  | _ => return ({} : Poly).insert (← internBase (castOf e)) 1

/-- Interning key for `b⁻¹`-shaped atoms: `x⁻¹` and `a / x` must land on the
same probe atom, like they do after stock's ring normalization. -/
private def invKey (b : Expr) : Expr := Expr.app (Expr.const ``Inv.inv []) b

/-- Numeric-only linear/polynomial form of an arithmetic expression.
Anything unrecognized becomes an opaque base atom. -/
private partial def parseForm (e : Expr) : ParseM Poly := do
  if let some q := e.rat? then return pconst q
  if let some q := scientific? e then return pconst q
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return padd (← parseForm a) (← parseForm b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return padd (← parseForm a) (pscale (-1) (← parseForm b))
  | (``Neg.neg, #[_, _, a]) => return pscale (-1) (← parseForm a)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      match a.rat?, b.rat? with
      | some c, _ => return pscale c (← parseForm b)
      | _, some c => return pscale c (← parseForm a)
      | _, _ => pmul (← parseForm a) (← parseForm b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
      -- KNOWN IMPRECISION: over ℤ/ℕ, `a / c` truncates, but the probe
      -- models it as exact division (the type is not visible here). Like
      -- ℕ-subtraction, this can only mis-select and fall back — never
      -- affect soundness.
      match b.rat? with
      | some c => if c == 0 then return pconst 0 else return pscale c⁻¹ (← parseForm a)
      | none =>
        -- mirror ring normalization: a / b = a * b⁻¹, so a shared
        -- denominator becomes a shared atom across hypotheses (the atom key
        -- is a hash-only Expr, it never needs to typecheck)
        pmul (← parseForm a) (({} : Poly).insert (← internBase (invKey b)) 1)
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
      match n.rat? with
      | some q =>
        if q == 2 then do let p ← parseForm a; pmul p p
        else if q == 1 then parseForm a
        else if q == 0 then return pconst 1
        else return ({} : Poly).insert (← internBase e) 1
      | none => return ({} : Poly).insert (← internBase e) 1
  | (``Inv.inv, #[_, _, a]) =>
      return ({} : Poly).insert (← internBase (invKey a)) 1
  | (n, #[_, _, a]) =>
      if isCastHead n then
        let castOf := fun leaf => Expr.app e.appFn! leaf
        parseCastForm castOf (n == ``Nat.cast || n == ``NatCast.natCast) a
      else
        return ({} : Poly).insert (← internBase e) 1
  | _ => return ({} : Poly).insert (← internBase e) 1

/-- A probe hypothesis: comparison `poly str 0`, its parent context proofs
(empty for synthetic facts), and whether the comparison lives in ℤ/ℕ. -/
structure ProbeHyp where
  /-- comparison strength (`poly str 0`) -/
  str : Mathlib.Ineq
  /-- sparse linear/polynomial form over probe atoms -/
  poly : Poly
  /-- context proofs this hyp derives from (what restriction selects) -/
  parents : List Expr
  /-- lives in ℤ/ℕ: strict comparisons strengthen by +1 -/
  intLike : Bool
  /-- lives in ℕ: atoms get nonnegativity facts (ℕ-subtraction distribution
  is blocked only under casts, via `parseCastForm`'s natSrc) -/
  natTyped : Bool := false

/-- Clear denominators (positive scale) and, over ℤ/ℕ, strengthen strict
comparisons: `t < 0` ⇒ `t + 1 ≤ 0`. Returns the integer Comp. -/
private def toComp (h : ProbeHyp) : Comp :=
  let denLcm : Nat := h.poly.fold (fun l _ v => Nat.lcm l v.den) 1
  let scaled : List (Nat × Int) := h.poly.toList.map fun (k, v) =>
    (k, (v * (denLcm : Rat)).num)
  if h.intLike && h.str == .lt then
    let shifted :=
      if scaled.any (·.1 == 0) then
        scaled.map fun (k, v) => if k == 0 then (k, v + 1) else (k, v)
      else (0, (1 : Int)) :: scaled
    ⟨.le, shifted⟩
  else
    ⟨h.str, scaled⟩

private def isIntLike (t : Expr) : Bool :=
  t.isConstOf ``Nat || t.isConstOf ``Int

-- No type whitelist: the probe is type-agnostic (atoms are opaque, only
-- rational literals become coefficients), ℕ/ℤ get their special semantics
-- via `isIntLike`/`natTyped`, and a semantically-wrong probe on an exotic
-- type merely mis-selects and falls back — it can never affect soundness.
-- (A ℕ/ℤ/ℚ/ℝ whitelist here cost a measured 0/21 blackout on generic-𝕜
-- files like Mathlib/Analysis/Convex/Slope.lean.)

/-- Parse `lhs R rhs` into a probe hyp (`lhs - rhs R 0`). -/
private def parseIneq (str : Mathlib.Ineq) (t lhs rhs : Expr) (parents : List Expr) :
    ParseM ProbeHyp := do
  let p := padd (← parseForm lhs) (pscale (-1) (← parseForm rhs))
  return { str, poly := p, parents, intLike := isIntLike t,
           natTyped := t.isConstOf ``Nat }

/-- nlinarith product of two probe hyps (post-normalization forms). -/
private def probeProduct (a b : ProbeHyp) : ParseM (Option ProbeHyp) := do
  let str : Mathlib.Ineq :=
    match a.str, b.str with
    | .eq, _ => .eq
    | _, .eq => .eq
    | .lt, .lt => .lt
    | _, _ => .le
  -- t1 R1 0, t2 R2 0  ⇒  t1*t2 {>,≥,=} 0  ⇒  -(t1*t2) {<,≤,=} 0
  let prod ← pmul a.poly b.poly
  return some { str, poly := pscale (-1) prod,
                parents := (a.parents ++ b.parents).eraseDups,
                intLike := a.intLike && b.intLike }

/-- Run one probe: build Comps, query the native oracle, return the parent
hypothesis set of the certificate (none = no certificate / any failure). -/
private def runProbe (hyps : List ProbeHyp) (maxVar : Nat) :
    MetaM (Option (List Expr)) := do
  -- mirror every equality (certificates need λ ≥ 0, so the reversed
  -- orientation must be present — exactly like addNegEqProofs in stock)
  let hyps := hyps.flatMap fun h =>
    if h.str == .eq then [h, { h with poly := pscale (-1) h.poly }] else [h]
  -- seed `-1 < 0` as hyp 0, exactly like proveFalseByLinarith
  let seed : ProbeHyp := { str := .lt, poly := pconst (-1), parents := [], intLike := false }
  let all := seed :: hyps
  let comps := all.map toComp
  try
    let cert ← Farkas.native.produceCertificate comps maxVar
    let mut parents : List Expr := []
    for (i, c) in cert.toList do
      if c > 0 then
        if let some h := all[i]? then
          parents := parents ++ h.parents
    return some parents.eraseDups
  catch _ => return none

/-- Run a pure parse action against a shared mutable ParseState. -/
private def runP (stRef : IO.Ref ParseState) (m : ParseM α) : MetaM α := do
  let s ← stRef.get
  let (a, s') := m.run s
  stRef.set s'
  return a

/-- Collect probe hyps from a hypothesis type, splitting conjunctions
(numeric mirror of the stock `splitConjunctions` preprocessor). -/
private partial def collectHyp (stRef : IO.Ref ParseState) (parent : Expr) (ty : Expr) :
    MetaM (List ProbeHyp) := do
  match ty.and? with
  | some (a, b) =>
    return (← collectHyp stRef parent a) ++ (← collectHyp stRef parent b)
  | none =>
    match ← tryCatch (some <$> ty.ineqOrNotIneq?) (fun _ => pure none) with
    | some (isPos, str, t, lhs, rhs) =>
      if isPos then
        return [← runP stRef (parseIneq str t lhs rhs [parent])]
      else
        -- mirror stock removeNegations: ¬(l < r) ⇒ r ≤ l, ¬(l ≤ r) ⇒ r < l;
        -- ¬(l = r) needs a case split — not expressible as one probe hyp
        match str with
        | .lt => return [← runP stRef (parseIneq .le t rhs lhs [parent])]
        | .le => return [← runP stRef (parseIneq .lt t rhs lhs [parent])]
        | .eq => return []
    | none => return []

open Farkas.Telemetry in
/-- Emit a `ty:"fast"` diagnostic row to the shared telemetry sink. -/
private def emitFast (fields : List (String × String)) : IO Unit :=
  Telemetry.emit <| row (("ty", jstr "fast") :: fields)

/-- EXPERIMENTAL (grind fact-selection prototype, see Farkas/GrindFast.lean):
run the numeric probe over the goal + local context and return the selected
parent hypotheses — no restricted run, no telemetry. `none` = probe
unavailable or missed; callers must fall back. -/
def probeSelect (nlin : Bool) (g : MVarId) : MetaM (Option (List Expr)) :=
  g.withContext do
    if (← Farkas.findBinary).isNone then return none
    let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
    let stRef : IO.Ref ParseState ← IO.mkRef {}
    let runP {α} : ParseM α → MetaM α := Farkas.Fast.runP stRef
    let goalBranches : Option (List ProbeHyp) ← do
      match ← tryCatch (some <$> tgt.ineqOrNotIneq?) (fun _ => pure none) with
      | some (isPos, str, t, lhs, rhs) =>
        if isPos then
          match str with
          | .lt => pure <| some [← runP (parseIneq .le t rhs lhs [])]
          | .le => pure <| some [← runP (parseIneq .lt t rhs lhs [])]
          | .eq => pure <| some [← runP (parseIneq .lt t lhs rhs []),
                                 ← runP (parseIneq .lt t rhs lhs [])]
        else
          pure <| some [← runP (parseIneq str t lhs rhs [])]
      | none =>
        if tgt.isConstOf ``False then pure (some [])
        else pure none
    let some goalBranches := goalBranches | return none
    let mut ctx : List ProbeHyp := []
    let mut natAtoms : Std.HashSet Nat := {}
    -- ℕ atoms appearing only in the (negated) goal still need their
    -- nonnegativity facts
    for gb in goalBranches do
      if gb.natTyped then
        for (k, _) in gb.poly.toList do
          if k != 0 then natAtoms := natAtoms.insert k
    for h in (← getLocalHyps) do
      let ty ← instantiateMVars (← inferType h)
      for ph in ← collectHyp stRef h ty do
        if ph.natTyped then
          for (k, _) in ph.poly.toList do
            if k != 0 then natAtoms := natAtoms.insert k
        ctx := ctx.cons ph
    if ctx.isEmpty && goalBranches.isEmpty then return none
    let mut synth : List ProbeHyp := []
    for a in natAtoms do
      synth := synth.cons
        { str := .le, poly := pscale (-1) (({} : Poly).insert a 1),
          parents := [], intLike := true }
    if nlin then
      let s ← stRef.get
      for (pid, i, j) in s.pairs do
        -- squares only: x·x ≥ 0 is a fact, x·y for distinct atoms is not
        if i == j then
          synth := synth.cons
            { str := .le, poly := pscale (-1) (({} : Poly).insert pid 1),
              parents := [], intLike := false }
    let branches := if goalBranches.isEmpty then [[]] else goalBranches.map ([·])
    let mut parents : Option (List Expr) := some []
    for gb in branches do
      let mut hyps := gb ++ ctx ++ synth
      if nlin then
        let pool := hyps
        let mut prods : List ProbeHyp := []
        for (a, i) in pool.zipIdx do
          for (b, j) in pool.zipIdx do
            if i ≤ j then
              if let some p ← runP (probeProduct a b) then
                prods := prods.cons p
        hyps := hyps ++ prods
      let maxVar := (← stRef.get).nextId - 1
      match ← runProbe hyps maxVar with
      | some ps => parents := parents.map (· ++ ps)
      | none => parents := none; break
    return parents.map (·.eraseDups)

/--
Try the probe-then-restrict fast path on the main goal. Returns `true` iff the
goal was closed. Never throws; `false` means the caller should run stock.

v2: `args` are extra proof terms from `linarith [t₁, …]` (already elaborated
by the frontend); with `onlyOn` the context is skipped entirely — the probe
pool is exactly the stock hypothesis pool for each form. Restriction always
runs `linarith true s` where `s` mixes selected fvars and arg terms; both are
just proof `Expr`s to stock only-mode.
-/
private def probeAndRestrict (nlin onlyOn : Bool) (args : List Expr)
    (cfg : LinarithConfig) (callId t0 : Nat) (g : MVarId) : TacticM Bool :=
    g.withContext do
      -- cleanupAnnotations: `by_contra`-style goals arrive as `False` under
      -- mdata, which defeats `isConstOf`/`ineqOrNotIneq?` (found via the
      -- goal-unparsed telemetry: 60/66 of a never-entered sample were
      -- literally `False`)
      let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
      -- parse under one shared ParseState (atoms must be consistent)
      let stRef : IO.Ref ParseState ← IO.mkRef {}
      let runP {α} : ParseM α → MetaM α := Farkas.Fast.runP stRef
      -- goal
      let goalBranches : Option (List ProbeHyp) ← do
        match ← tryCatch (some <$> tgt.ineqOrNotIneq?) (fun _ => pure none) with
        | some (isPos, str, t, lhs, rhs) =>
          if isPos then
            match str with
            | .lt => pure <| some [← runP (parseIneq .le t rhs lhs [])]
            | .le => pure <| some [← runP (parseIneq .lt t rhs lhs [])]
            | .eq => pure <| some [← runP (parseIneq .lt t lhs rhs []),
                                   ← runP (parseIneq .lt t rhs lhs [])]
          else
            -- ¬ (lhs str rhs): the comparison itself becomes a hypothesis
            pure <| some [← runP (parseIneq str t lhs rhs [])]
        | none =>
          if tgt.isConstOf ``False then pure (some [])
          else pure none   -- exfalso-style goals: v1 falls back
      let some goalBranches := goalBranches
        | do
          if (← IO.getEnv "FARKAS_FAST_DEBUG") == some "1" then
            emitFast [("call", toString callId), ("outcome", "\"goal-unparsed\""),
                      ("goal", Telemetry.jstrEsc (toString (← Meta.ppExpr tgt)))]
          return false
      -- hypothesis pool: context (unless only-mode) + explicit arg terms,
      -- conjunctions split numerically
      let sources : List Expr ← do
        if onlyOn then pure args
        else pure ((← getLocalHyps).toList ++ args)
      let mut ctx : List ProbeHyp := []
      let mut natAtoms : Std.HashSet Nat := {}
      -- ℕ atoms appearing only in the (negated) goal still need their
      -- nonnegativity facts
      for gb in goalBranches do
        if gb.natTyped then
          for (k, _) in gb.poly.toList do
            if k != 0 then natAtoms := natAtoms.insert k
      for h in sources do
        let ty ← instantiateMVars (← inferType h)
        for ph in ← collectHyp stRef h ty do
          if ph.natTyped then
            for (k, _) in ph.poly.toList do
              if k != 0 then natAtoms := natAtoms.insert k
          ctx := ctx.cons ph
      if ctx.isEmpty && goalBranches.isEmpty then
        if (← IO.getEnv "FARKAS_FAST_DEBUG") == some "1" then
          emitFast [("call", toString callId), ("outcome", "\"empty-pool\"")]
        return false
      -- synthetic facts: ℕ nonnegativity + (nlinarith) square nonnegativity
      let mut synth : List ProbeHyp := []
      for a in natAtoms do
        synth := synth.cons
          { str := .le, poly := pscale (-1) (({} : Poly).insert a 1),
            parents := [], intLike := true }
      if nlin then
        let s ← stRef.get
        for (pid, i, j) in s.pairs do
          -- squares only: x·x ≥ 0 is a fact, x·y for distinct atoms is not
          if i == j then
            synth := synth.cons
              { str := .le, poly := pscale (-1) (({} : Poly).insert pid 1),
                parents := [], intLike := false }
      -- probe each goal branch; collect union of parents
      let tParse ← IO.monoNanosNow
      let branches := if goalBranches.isEmpty then [[]] else goalBranches.map ([·])
      let mut parents : Option (List Expr) := some []
      let mut missedBranch : List ProbeHyp := []
      for gb in branches do
        let mut hyps := gb ++ ctx ++ synth
        if nlin then
          -- pairwise products over the full pool, mirroring stock
          -- nlinarithExtras' products over (squares ++ post-natToInt hyps)
          let pool := hyps
          let mut prods : List ProbeHyp := []
          for (a, i) in pool.zipIdx do
            for (b, j) in pool.zipIdx do
              if i ≤ j then
                if let some p ← runP (probeProduct a b) then
                  prods := prods.cons p
          hyps := hyps ++ prods
        let maxVar := (← stRef.get).nextId - 1
        match ← runProbe hyps maxVar with
        | some ps => parents := parents.map (· ++ ps)
        | none => parents := none; missedBranch := gb; break
      let tOracle ← IO.monoNanosNow
      if parents.isNone then
        let mut dbg : List (String × String) := []
        if (← IO.getEnv "FARKAS_FAST_DEBUG") == some "1" then
          -- dump the branch that actually missed (eq goals probe two)
          let missedHyps := missedBranch ++ ctx ++ synth
          dbg := [("probeComps",
            "[" ++ ",".intercalate (missedHyps.map (Telemetry.compJson ∘ toComp)) ++ "]")]
        emitFast <| [("call", toString callId), ("outcome", "\"probe-miss\""),
                  ("nsParse", toString (tParse - t0)),
                  ("nsOracle", toString (tOracle - tParse))] ++ dbg
        return false
      let s := (parents.getD []).eraseDups
      -- restricted stock run on the selected hypotheses
      tryCatch
        (do
          Mathlib.Tactic.Linarith.linarith true s cfg g
          replaceMainGoal []
          let t1 ← IO.monoNanosNow
          emitFast [("call", toString callId), ("outcome", "\"hit\""),
                    ("nS", toString s.length), ("nCtx", toString ctx.length),
                    ("nArgs", toString args.length),
                    ("only", if onlyOn then "true" else "false"),
                    ("nsParse", toString (tParse - t0)),
                    ("nsOracle", toString (tOracle - tParse)),
                    ("nsTotal", toString (t1 - t0))]
          return true)
        (fun _ => do
          emitFast [("call", toString callId), ("outcome", "\"restricted-fail\""),
                    ("nS", toString s.length)]
          return false)

/--
Try the probe-then-restrict fast path on the main goal. Returns `true` iff the
goal was closed. Never throws; `false` means the caller should run stock.
-/
def tryFast (nlin onlyOn : Bool) (args : List Expr) (cfg : LinarithConfig)
    (callId : Nat) : TacticM Bool := do
  if (← Farkas.findBinary).isNone then
    Farkas.warnOnceMissing
    return false
  let t0 ← IO.monoNanosNow
  let g ← getMainGoal
  tryCatch (probeAndRestrict nlin onlyOn args cfg callId t0 g)
    (fun _ => do
      emitFast [("call", toString callId), ("outcome", "\"probe-error\"")]
      return false)

end Farkas.Fast
