/-
Native certificate oracle: a `Linarith.CertificateOracle` backed by
`farkas-oracled` (the Rust tiered exact engine), spoken to over a
line-oriented stdin/stdout protocol (docs/protocol.md). The daemon is a
local child process (polyrith lesson: no remote services), spawned lazily on
first use and kept alive for the rest of the Lean process.

Binary discovery: see `Farkas.findBinary` (Platform.lean) — a missing binary
degrades to stock behavior. Soundness: the certificate is re-checked by
linarith's proof reconstruction (`ring`), so a wrong answer can only cause a
tactic failure, never a wrong proof. The daemon additionally exact-verifies
every cert before answering.
-/
import Mathlib.Tactic.Linarith.Datatypes
import Farkas.Platform
import Farkas.Telemetry

open Lean Mathlib.Tactic.Linarith

namespace Farkas

private abbrev DaemonProc :=
  IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }

private def spawnDaemon : IO DaemonProc := do
  let some bin ← findBinary
    | throw <| IO.userError
        "Farkas.native: no daemon binary (set FARKAS_NATIVE_BIN or put farkas-oracled on PATH)"
  IO.Process.spawn
    { cmd := bin, args := #["--serve"],
      stdin := .piped, stdout := .piped, stderr := .inherit }

/-- Spawn + handshake (docs/protocol.md): the daemon must report
`farkas_protocol == 1`. A mismatch throws here, which call sites turn into
a soft degradation to stock behavior. -/
private def spawnAndHandshake : IO DaemonProc := do
  let c ← spawnDaemon
  c.stdin.putStr "{\"hello\":true}\n"
  c.stdin.flush
  let line ← c.stdout.getLine
  let v1 := match Json.parse line >>= (·.getObjValAs? Nat "farkas_protocol") with
    | .ok 1 => true
    | _ => false
  unless v1 do
    throw <| IO.userError s!"farkas-oracled protocol mismatch: {line.trimAscii}"
  return c

/-- The daemon slot, behind a mutex: Lean elaborates declarations in
parallel, and the line protocol requires each request/response round-trip
to be atomic — unlocked, interleaved writers could corrupt requests or
swap responses between callers. -/
initialize daemonMutex : Std.Mutex (Option DaemonProc) ← Std.Mutex.new none

/-- Drop a (presumed dead) daemon handle so the next call respawns. -/
private def resetDaemon : IO Unit :=
  daemonMutex.atomically (set (none : Option DaemonProc))

private def requestLine (hyps : List Comp) (maxVar : Nat) : String :=
  let hj := hyps.map Telemetry.compJson
  s!"\{\"maxVar\":{maxVar},\"hyps\":[{",".intercalate hj}]}"

private def parseCert (line : String) : Except String (Std.HashMap Nat Nat) := do
  let j ← Json.parse line
  match j.getObjVal? "cert" with
  | .ok (Json.arr entries) =>
    let mut m : Std.HashMap Nat Nat := {}
    for e in entries do
      match e with
      | Json.arr #[i, Json.str c] =>
        let i ← i.getNat?
        let some n := c.toNat? | throw s!"bad coefficient {c}"
        m := m.insert i n
      | _ => throw s!"bad cert entry {e}"
    return m
  | .ok Json.null => throw "no certificate"
  | _ => throw s!"bad response: {line}"

/-- One locked round-trip (lazy spawn + handshake on first use); IO errors
(dead daemon, protocol mismatch) propagate.

KNOWN LIMITATION: the read has no timeout, so a daemon that *hangs* (as
opposed to crashing) would block callers on the mutex. The shipped daemon
is fuzz-tested to always answer (tests/daemon_fuzz.rs); a hostile
`FARKAS_NATIVE_BIN` binary is outside the threat model (it runs with the
user's own privileges anyway).

Retry note: the one-respawn retry in `native` is not atomic with this
round-trip; two threads racing a dead daemon can cause one extra respawn.
Harmless: the orphaned handle's stdin drops, so the extra process exits
on EOF. -/
private def queryDaemon (req : String) : IO String :=
  daemonMutex.atomically do
    let c ← do
      match ← get with
      | some c => pure c
      | none =>
        let c ← spawnAndHandshake
        set (some c)
        pure c
    c.stdin.putStr (req ++ "\n")
    c.stdin.flush
    let line ← c.stdout.getLine
    if line.isEmpty then
      -- EOF: daemon died; drop the handle so the next call respawns
      set (none : Option DaemonProc)
      throw <| IO.userError "farkas-oracled daemon exited"
    return line

/--
`CertificateOracle` backed by the native tiered exact engine.
Use as `linarith (oracle := Farkas.native)` or via the instrumentation
layer's `FARKAS_ORACLE=native` switch.
-/
def native : CertificateOracle where
  produceCertificate hyps maxVar := do
    let req := requestLine hyps maxVar
    let line ← try queryDaemon req
      catch _ =>
        -- one respawn attempt (a broken-pipe write leaves a dead handle)
        resetDaemon
        queryDaemon req
    match parseCert line with
    | .ok m => return m
    | .error e => throwError "Farkas.native: {e}"

end Farkas
