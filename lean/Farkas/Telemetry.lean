/-
Shared JSONL telemetry sink and JSON helpers for the oracle client, the fast
path, and the instrumentation layer.

Rows are appended to `$FARKAS_CORPUS_FILE`; no-op when unset. The same
`Comp` serialization doubles as the daemon request format (docs/protocol.md).
-/
import Mathlib.Tactic.Linarith.Datatypes

open Mathlib.Tactic.Linarith

namespace Farkas.Telemetry

/-- JSON string literal (no escaping; keys and known-safe values only). -/
def jstr (s : String) : String := "\"" ++ s ++ "\""

/-- JSON string with escaping, for payloads that may contain quotes. -/
def jstrEsc (s : String) : String :=
  "\"" ++ s.foldl (fun a c =>
    a ++ if c == '"' then "\\\"" else if c == '\\' then "\\\\"
         else if c == '\n' then "\\n" else toString c) "" ++ "\""

/-- One JSON object from preformatted key/value fragments. -/
def row (fields : List (String × String)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => jstr k ++ ":" ++ v) ++ "}"

/-- `Ineq` as its protocol tag (`"lt" | "le" | "eq"`). -/
def ineqJson : Mathlib.Ineq → String
  | .eq => jstr "eq"
  | .le => jstr "le"
  | .lt => jstr "lt"

/-- `Comp` in the shared wire/telemetry shape `[tag, [[atom, coeff], …]]`. -/
def compJson (c : Comp) : String :=
  let cs := c.coeffs.map fun (i, a) => s!"[{i},{a}]"
  s!"[{ineqJson c.str},[{",".intercalate cs}]]"

/-- Append one JSONL row to `$FARKAS_CORPUS_FILE` (no-op when unset). -/
def emit (s : String) : IO Unit := do
  if let some path ← IO.getEnv "FARKAS_CORPUS_FILE" then
    try
      let h ← IO.FS.Handle.mk path .append
      h.putStrLn s
      h.flush
    catch _ => pure ()

end Farkas.Telemetry
