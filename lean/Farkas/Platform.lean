/-
Daemon binary discovery. Deliberately Mathlib-free: `Farkas.Fetch` (the
`lake exe farkas-fetch` downloader) must build before Mathlib does.
-/

namespace Farkas

/-- Platform-correct daemon binary filename. -/
def binaryName : String :=
  if System.Platform.isWindows then "farkas-oracled.exe" else "farkas-oracled"

/--
Locate the daemon binary. Order:
1. `FARKAS_NATIVE_BIN` env var (escape hatch / CI pinning);
2. the package-local artifact slot `.lake/farkas/` populated by
   `lake exe farkas-fetch`;
3. `farkas-oracled` on `PATH`.
Returns `none` when no binary is available — callers must degrade to stock
behavior; a missing binary must never break a build.
-/
def findBinary : IO (Option String) := do
  if let some p ← IO.getEnv "FARKAS_NATIVE_BIN" then
    return some p
  let slot : System.FilePath := ".lake" / "farkas" / binaryName
  if ← slot.pathExists then
    return some slot.toString
  if let some path ← IO.getEnv "PATH" then
    let sep := if System.Platform.isWindows then ";" else ":"
    for dir in path.splitOn sep do
      if dir.isEmpty then continue
      let cand : System.FilePath := System.FilePath.mk dir / binaryName
      if ← cand.pathExists then
        return some cand.toString
  return none

/-- Process-wide "already warned about the missing daemon" flag. -/
initialize warnedRef : IO.Ref Bool ← IO.mkRef false

/-- One-time note when the fast path is unavailable. -/
def warnOnceMissing : IO Unit := do
  unless ← warnedRef.modifyGet fun w => (w, true) do
    IO.eprintln
      "farkas: daemon binary not found; using stock linarith \
       (install farkas-oracled or set FARKAS_NATIVE_BIN)"

end Farkas
