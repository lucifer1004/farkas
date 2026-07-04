#!/usr/bin/env python3
"""Differential gate: run Mathlib's own linarith test
files stock vs fast-path and assert bit-identical outcomes.

For each watched MathlibTest file we produce two copies that differ ONLY by
`import Farkas.Auto` (the drop-in shadow-elab activation):

  stock copy: file as-is
  fast copy:  file + `import Farkas.Auto`   (fast path is on by default)

and compare exit code + normalized diagnostics. Any divergence is a gate
failure: the fast path's contract is "bit-identical behavior, only faster".

Both copies get the same mechanical header transform (drop the `module`
keyword, `meta def` -> `def`): module files cannot import our non-module
package, and applying it to BOTH sides keeps the comparison honest.

Usage: scripts/differential.py [--keep] [FILE ...]
  FILE: explicit .lean files to gate (default: the watched MathlibTest set
        plus lean/tests/fast_corners.lean).
Requires: `lake build` done, daemon available (fetch slot / FARKAS_NATIVE_BIN).
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import lean_wrap

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"
MATHLIB_TESTS = LEAN_DIR / ".lake" / "packages" / "mathlib" / "MathlibTest"

DEFAULT_FILES = [
    MATHLIB_TESTS / "Tactic" / "Linarith" / "Basic.lean",
    MATHLIB_TESTS / "Tactic" / "Linarith" / "NNReal.lean",
    LEAN_DIR / "tests" / "fast_corners.lean",
]


def transform(text: str, inject_farkas: bool) -> str:
    return lean_wrap.wrap_source(
        text, "import Farkas.Auto" if inject_farkas else None
    )


def run_lean(path: Path, env_extra: dict) -> tuple[int, str]:
    env = os.environ.copy()
    env.update(env_extra)
    p = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=LEAN_DIR,
        env=env,
        capture_output=True,
        text=True,
        timeout=1800,
    )
    return p.returncode, p.stdout + p.stderr


def normalize(output: str, path: Path) -> str:
    out = output.replace(str(path), "FILE").replace(path.name, "FILE")
    out = re.sub(r"\x1b\[[0-9;]*m", "", out)  # ANSI
    return out.strip()


def gate(src: Path, workdir: Path) -> bool:
    text = src.read_text()
    stock = workdir / f"stock_{src.stem}.lean"
    fast = workdir / f"fast_{src.stem}.lean"
    stock.write_text(transform(text, inject_farkas=False))
    fast.write_text(transform(text, inject_farkas=True))

    # FARKAS_FAST unset -> default on; stock copy has no Farkas import at all
    code_s, out_s = run_lean(stock, {})
    code_f, out_f = run_lean(fast, {})
    out_s, out_f = normalize(out_s, stock), normalize(out_f, fast)

    if code_s == code_f and out_s == out_f:
        print(f"PASS {src.name}  (exit {code_s}, {len(out_s.splitlines())} diag lines)")
        return True
    print(f"DIFF {src.name}: stock exit {code_s} vs fast exit {code_f}")
    import difflib

    for l in difflib.unified_diff(
        out_s.splitlines(), out_f.splitlines(), "stock", "fast", lineterm=""
    ):
        print(f"  {l}")
    return False


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="*", type=Path)
    ap.add_argument("--keep", action="store_true", help="keep the work dir")
    args = ap.parse_args()

    files = args.files or DEFAULT_FILES
    missing = [f for f in files if not f.exists()]
    if missing:
        print(f"ERROR: missing test files: {missing}", file=sys.stderr)
        return 2

    workdir = Path(tempfile.mkdtemp(prefix="farkas-diff-"))
    try:
        results = [gate(f, workdir) for f in files]
    finally:
        if args.keep:
            print(f"work dir kept: {workdir}")
        else:
            shutil.rmtree(workdir, ignore_errors=True)
    failed = results.count(False)
    print(f"differential gate: {len(results) - failed}/{len(results)} identical")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
