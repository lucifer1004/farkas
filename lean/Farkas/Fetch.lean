/-
`lake exe farkas-fetch` — download the prebuilt `farkas-oracled` daemon for
the host platform from GitHub Releases into the `.lake/farkas/` artifact slot
(the second stop of `Farkas.findBinary`'s discovery chain).

Deliberately Mathlib-free (imports only `Farkas.Platform`), so the
executable builds and runs before (and independently of) the main library.
External tools used are present on every supported platform out of the box:
`curl`, `tar` (bsdtar ships with Windows 10+), and a sha256 utility
(`sha256sum` / `shasum` / `certutil`).

Overrides:
  FARKAS_FETCH_TAG       release tag (default: `defaultTag` below)
  FARKAS_FETCH_BASE_URL  directory URL holding the artifacts + SHA256SUMS
                         (testing / mirrors; `file://` URLs work)

Failure is loud and safe: any error leaves stock linarith behavior intact and
prints the cargo-build fallback.
-/
import Farkas.Platform

namespace Farkas.Fetch

def defaultTag : String := "v4.31.0-farkas.1"

def defaultBase : String :=
  "https://github.com/lucifer1004/farkas/releases/download"

def binaryName : String := Farkas.binaryName

def run (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode != 0 then
    throw <| IO.userError s!"`{cmd} {" ".intercalate args.toList}` failed \
      (exit {out.exitCode}): {out.stderr.trimAscii.toString}"
  return out.stdout

/-- Release-artifact target triple for the host. -/
def target : IO String := do
  if System.Platform.isWindows then
    -- the only Windows artifact we build; arm windows falls back to cargo
    return "x86_64-pc-windows-msvc"
  let arch := (← run "uname" #["-m"]).trimAscii.toString
  let arch := if arch == "arm64" then "aarch64" else arch
  match System.Platform.isOSX, arch with
  | true,  "aarch64" => return "aarch64-apple-darwin"
  | true,  "x86_64"  => return "x86_64-apple-darwin"
  | false, "aarch64" => return "aarch64-unknown-linux-musl"
  | false, "x86_64"  => return "x86_64-unknown-linux-musl"
  | _, a => throw <| IO.userError s!"no prebuilt artifact for arch `{a}`"

/-- Lower-case hex sha256 of a file, via the platform's stock utility. -/
def sha256File (f : String) : IO String := do
  if System.Platform.isWindows then
    -- output: header line, hash line (possibly space-grouped), footer
    let out ← run "certutil" #["-hashfile", f, "SHA256"]
    match out.splitOn "\n" |>.filter (fun l => !l.trimAscii.toString.isEmpty) with
    | _ :: h :: _ => return (h.trimAscii.toString.replace " " "").toLower
    | _ => throw <| IO.userError "certutil: unexpected output"
  else
    let cmd := if System.Platform.isOSX then ("shasum", #["-a", "256", f])
               else ("sha256sum", #[f])
    let out ← run cmd.1 cmd.2
    match out.splitOn " " with
    | h :: _ => return h.toLower
    | _ => throw <| IO.userError s!"{cmd.1}: unexpected output"

/-- Find `artifact`'s hash in a `sha256sum`-format SHA256SUMS body. -/
def lookupSum (sums artifact : String) : Option String :=
  sums.splitOn "\n" |>.firstM fun l =>
    match l.trimAscii.toString.splitOn " " |>.filter (fun s => !s.isEmpty) with
    | [h, n] => if n == artifact || n == s!"*{artifact}" then some h.toLower else none
    | _ => none

def fetch : IO Unit := do
  let tag := (← IO.getEnv "FARKAS_FETCH_TAG").getD defaultTag
  let base := (← IO.getEnv "FARKAS_FETCH_BASE_URL").getD s!"{defaultBase}/{tag}"
  let artifact := s!"farkas-oracled-{← target}.tar.gz"
  let dir : System.FilePath := ".lake" / "farkas"
  IO.FS.createDirAll dir
  let artPath := dir / artifact
  let sumsPath := dir / "SHA256SUMS"
  IO.println s!"farkas-fetch: downloading {base}/{artifact}"
  discard <| run "curl" #["-fsSL", "--retry", "3", "-o", artPath.toString,
                          s!"{base}/{artifact}"]
  discard <| run "curl" #["-fsSL", "--retry", "3", "-o", sumsPath.toString,
                          s!"{base}/SHA256SUMS"]
  let some expected := lookupSum (← IO.FS.readFile sumsPath) artifact
    | throw <| IO.userError s!"SHA256SUMS has no entry for {artifact}"
  let actual ← sha256File artPath.toString
  unless actual == expected do
    IO.FS.removeFile artPath
    throw <| IO.userError
      s!"sha256 mismatch for {artifact}: expected {expected}, got {actual}"
  discard <| run "tar" #["-xzf", artPath.toString, "-C", dir.toString]
  IO.FS.removeFile artPath
  let bin := dir / binaryName
  unless System.Platform.isWindows do
    discard <| run "chmod" #["+x", bin.toString]
  -- smoke: the unpacked daemon must identify itself
  let v ← run bin.toString #["--version"]
  IO.println s!"farkas-fetch: installed {bin} ({v.trimAscii.toString})"

end Farkas.Fetch

def main (_ : List String) : IO UInt32 := do
  try
    Farkas.Fetch.fetch
    return 0
  catch e =>
    IO.eprintln s!"farkas-fetch: {e.toString}"
    IO.eprintln "farkas-fetch: fallback — `cargo build --release` in \
      oracle/native, then export FARKAS_NATIVE_BIN=<path to farkas-oracled>"
    return 1
