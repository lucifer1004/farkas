#!/usr/bin/env python3
"""farkas-corpus — reproduce the farkas measurement corpus from public
sources (recipe-not-payloads: the public benchmark is a harness + recipe,
the payloads are never redistributed — see docs/corpus.md).

Sources:
  acquire --from-dsv2       download DeepSeek-Prover-V2's official
                            minif2f-solutions.zip at runtime (never commit it)
  (--from-dir is not an acquire step: pass any directory of .lean proof
   files — your own RL traces, prover outputs — straight to replay/diff)
  --from-mathlib            Mathlib's own linarith test files (zero-license
                            smoke set, already on disk via lake)

Stages:
  replay --src DIR --out RUN     instrumented replay -> oracle JSONL corpus
  diff   --src DIR --out RUN     stock vs fast outcome differential
  report --run RUN               size/timing tables (analyze.py) + cert
                                 semantics validation (validate_spec.py)

Typical full recipe:
  scripts/farkas-corpus.py acquire --from-dsv2
  scripts/farkas-corpus.py replay --src corpus/dsv2-download --out corpus/myrun
  scripts/farkas-corpus.py report --run corpus/myrun
"""

import argparse
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"
LEAN_DIR = ROOT / "lean"
DSV2_URL = (
    "https://github.com/deepseek-ai/DeepSeek-Prover-V2/raw/main/minif2f-solutions.zip"
)
MATHLIB_LINARITH_TESTS = (
    LEAN_DIR / ".lake" / "packages" / "mathlib" / "MathlibTest" / "Tactic" / "Linarith"
)


def sh(cmd, **kw):
    print(f"+ {' '.join(str(c) for c in cmd)}", flush=True)
    return subprocess.run([str(c) for c in cmd], check=True, **kw)


def acquire(args) -> int:
    dest = pathlib.Path(args.dest).resolve()
    if dest.exists() and any(dest.rglob("*.lean")):
        print(f"{dest} already populated; delete it to re-download")
        return 0
    dest.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="farkas-corpus-") as td:
        zip_path = pathlib.Path(td) / "solutions.zip"
        sh(["curl", "-fSL", "--retry", "3", "-o", zip_path, args.url])
        sh(["unzip", "-q", zip_path, "-d", dest])
    n = len(list(dest.rglob("*.lean")))
    print(f"acquired {n} .lean files -> {dest}")
    print("NOTE: redistribution license unclear — keep these files local "
          "(the directory is gitignored); ship statistics, not payloads.")
    return 0 if n else 1


def resolve_src(args) -> pathlib.Path:
    if getattr(args, "from_mathlib", False):
        if not MATHLIB_LINARITH_TESTS.is_dir():
            sys.exit("mathlib not fetched — run `lake build` in lean/ first")
        return MATHLIB_LINARITH_TESTS
    if not args.src:
        sys.exit("need --src DIR (or --from-mathlib)")
    return pathlib.Path(args.src).resolve()


def replay(args) -> int:
    src = resolve_src(args)
    cmd = [sys.executable, SCRIPTS / "replay.py", "--src", src, "--out", args.out,
           "--jobs", args.jobs]
    if args.limit:
        cmd += ["--limit", args.limit]
    if getattr(args, "stock", False):
        cmd += ["--stock"]
    return sh(cmd).returncode


def load_outcomes(run_dir: pathlib.Path) -> dict:
    import json

    outcomes = {}
    for line in open(run_dir / "files.jsonl"):
        r = json.loads(line)
        outcomes[r["src"]] = r["exit"]
    return outcomes


def diff(args) -> int:
    """Outcome differential at corpus scale: every file must compile to the
    same exit status stock vs fast. (The per-PR diagnostic-exact gate is
    scripts/differential.py; this one is for nightly-sized sets.)"""
    src = resolve_src(args)
    out = pathlib.Path(args.out).resolve()
    for mode, extra in (("stock", ["--stock"]), ("fast", [])):
        cmd = [sys.executable, SCRIPTS / "replay.py", "--src", src,
               "--out", out / mode, "--jobs", args.jobs] + extra
        if args.limit:
            cmd += ["--limit", args.limit]
        sh(cmd)
    stock, fast = load_outcomes(out / "stock"), load_outcomes(out / "fast")
    diverged = sorted(
        s for s in stock.keys() | fast.keys() if stock.get(s) != fast.get(s)
    )
    for s in diverged:
        print(f"DIVERGED {s}: stock exit {stock.get(s)} vs fast exit {fast.get(s)}")
    print(f"outcome differential: {len(stock) - len(diverged)}/{len(stock)} identical")
    return 1 if diverged else 0


def grind_check(args) -> int:
    """Successor watch: textually substitute linarith/nlinarith -> grind and
    compare per-file compile outcomes vs the originals. Directional data for
    the quarterly grind-migration review, not a semantics-precise gate."""
    import re, tempfile
    src = resolve_src(args)
    out = pathlib.Path(args.out).resolve()
    orig_dir, sub_dir = out / "orig", out / "grind"
    for d in (orig_dir, sub_dir):
        d.mkdir(parents=True, exist_ok=True)
    files = sorted(src.rglob("*.lean"))
    if args.limit:
        files = files[: args.limit]
    for f in files:
        text = f.read_text()
        name = f.parent.name + "_" + f.name
        (orig_dir / name).write_text(text)
        (sub_dir / name).write_text(
            re.sub(r"\bnlinarith\b", "grind", re.sub(r"\blinarith\b", "grind", text)))
    results = {}
    for d in (orig_dir, sub_dir):
        cmd = [sys.executable, SCRIPTS / "replay.py", "--src", d,
               "--out", out / (d.name + "-run"), "--jobs", args.jobs, "--stock"]
        sh(cmd)
        results[d.name] = load_outcomes(out / (d.name + "-run"))
    # normalize keys: replay tags rows as <parent-dir>/<file>, and the
    # parent dir differs between the two variants
    norm = lambda d: {k.split("/", 1)[-1]: v for k, v in d.items()}
    orig, grind = norm(results["orig"]), norm(results["grind"])
    reg = sorted(s for s in orig if orig[s] == 0 and grind.get(s) != 0)
    gain = sorted(s for s in grind if grind[s] == 0 and orig.get(s) != 0)
    n_o = sum(1 for v in orig.values() if v == 0)
    n_g = sum(1 for v in grind.values() if v == 0)
    print(f"grind-check: linarith {n_o}/{len(orig)} clean, grind {n_g}/{len(grind)} clean; "
          f"takeover {n_o - len(reg)}/{n_o}, regressions {len(reg)}, gains {len(gain)}")
    for s_ in reg[:10]:
        print(f"  REGRESSION {s_}")
    return 0


def report(args) -> int:
    run = pathlib.Path(args.run).resolve()
    validate = ROOT / "oracle" / "validate_spec.py"
    rc = 0
    for cmd in ([sys.executable, SCRIPTS / "analyze.py", run],
                [sys.executable, validate, "--corpus", run]):
        print(f"+ {' '.join(str(c) for c in cmd)}", flush=True)
        rc |= subprocess.run([str(c) for c in cmd], check=False).returncode
    return rc


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    a = sub.add_parser("acquire", help="download a public corpus source")
    a.add_argument("--from-dsv2", action="store_true", required=True)
    a.add_argument("--url", default=DSV2_URL)
    a.add_argument("--dest", default=str(ROOT / "corpus" / "dsv2-download"))
    a.set_defaults(fn=acquire)

    for name, fn in (("replay", replay), ("diff", diff), ("grind-check", grind_check)):
        p = sub.add_parser(name)
        p.add_argument("--src", help="directory of .lean proof files")
        p.add_argument("--from-mathlib", action="store_true",
                       help="use Mathlib's own linarith test files as source")
        p.add_argument("--out", required=True)
        p.add_argument("--jobs", type=int, default=8)
        p.add_argument("--limit", type=int, default=0)
        if name == "replay":
            p.add_argument("--stock", action="store_true")
        p.set_defaults(fn=fn)

    r = sub.add_parser("report")
    r.add_argument("--run", required=True)
    r.set_defaults(fn=report)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
