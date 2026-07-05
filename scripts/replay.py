#!/usr/bin/env python3
"""Batch replay harness.

Replays a directory of Lean proof files (default: the DeepSeek-Prover-V2
miniF2F corpus, see docs/corpus.md) with the farkas instrumentation active,
collecting:
  - per-oracle-call corpus rows (JSONL, from the instrumented tactic),
  - per-file wall time + exit status (harness-side),
with N parallel workers to also produce a realistic arrival pattern.

Usage:
  python3 scripts/replay.py [--src DIR] [--jobs N] [--limit K] [--out corpus/myrun]

Each worker compiles one solution file via `lake env lean <wrapper>` where the
wrapper prepends `import Farkas.Instrument` after the Mathlib import so
the shadow elaborators intercept every (n)linarith call in the file.
`--stock` skips the instrumentation import (baseline outcomes only — a
placeholder line keeps diagnostics line-number-comparable); `module`-marked
sources get the same header transform as scripts/differential.py, applied
identically in both modes.
"""
import argparse
import json
import os
import pathlib
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

import lean_wrap

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"
SOLUTIONS = ROOT / "corpus" / "dsv2-download"  # from farkas-corpus acquire


def make_wrapper(src: pathlib.Path, wrapper_dir: pathlib.Path,
                 instrument: bool = True) -> pathlib.Path:
    """Instrumented (or line-aligned stock) compile wrapper for one file."""
    inject = "import Farkas.Instrument" if instrument else None
    out = wrapper_dir / f"{src.parent.name}__{src.name}"
    out.write_text(lean_wrap.wrap_source(src.read_text(), inject))
    return out


def run_one(src: pathlib.Path, out_dir: pathlib.Path, wrapper_dir: pathlib.Path,
            instrument: bool = True) -> dict:
    wrapper = make_wrapper(src, wrapper_dir, instrument)
    tag = f"{src.parent.name}/{src.name}"
    corpus_file = out_dir / f"oracle.{src.parent.name}.{src.stem}.jsonl"
    env = os.environ | {
        "FARKAS_CORPUS_FILE": str(corpus_file),
        "FARKAS_SRC": tag,
    }
    t0 = time.monotonic_ns()
    proc = subprocess.run(
        ["lake", "env", "lean", str(wrapper)],
        cwd=LEAN_DIR, env=env, capture_output=True, text=True, timeout=1800,
    )
    t1 = time.monotonic_ns()
    return {
        "ty": "file",
        "src": tag,
        "wallNs": t1 - t0,
        "t": t0,
        "exit": proc.returncode,
        "stderrTail": proc.stderr[-500:] if proc.returncode != 0 else "",
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", type=str, default=str(SOLUTIONS),
                    help="directory of .lean proof files (searched recursively)")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--limit", type=int, default=0, help="only first K files (0 = all)")
    ap.add_argument("--out", type=str, default=str(ROOT / "corpus" / "run1"))
    ap.add_argument("--stock", action="store_true",
                    help="no instrumentation import: baseline outcomes only")
    args = ap.parse_args()

    out_dir = pathlib.Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    wrapper_dir = out_dir / "wrappers"
    wrapper_dir.mkdir(exist_ok=True)

    src_dir = pathlib.Path(args.src).resolve()
    files = sorted(f for f in src_dir.rglob("*.lean") if "wrappers" not in f.parts)
    if args.limit:
        files = files[: args.limit]
    print(f"replaying {len(files)} files with {args.jobs} workers -> {out_dir}"
          + (" [stock]" if args.stock else ""))

    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = {pool.submit(run_one, f, out_dir, wrapper_dir,
                            not args.stock): f for f in files}
        for i, fut in enumerate(as_completed(futs), 1):
            try:
                r = fut.result()
            except subprocess.TimeoutExpired:
                f_ = futs[fut]
                r = {"ty": "file", "src": f"{f_.parent.name}/{f_.name}", "exit": -1,
                     "wallNs": 1800 * 10**9, "t": 0, "stderrTail": "TIMEOUT"}
            results.append(r)
            status = "ok" if r["exit"] == 0 else f"EXIT {r['exit']}"
            print(f"[{i}/{len(files)}] {r['src']}: {status} "
                  f"({r['wallNs'] / 1e9:.1f}s)", flush=True)

    with open(out_dir / "files.jsonl", "w") as fh:
        for r in results:
            fh.write(json.dumps(r) + "\n")

    n_ok = sum(1 for r in results if r["exit"] == 0)
    print(f"done: {n_ok}/{len(results)} files compiled clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
