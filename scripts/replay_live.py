#!/usr/bin/env python3
"""Live-REPL replay: one live REPL process per worker, Mathlib imported ONCE,
each solution theorem submitted as an incremental command against env 0.

Measures the *marginal* cost per theorem (statement elaboration + tactic
execution) with import fully amortized — the denominator that keep-alive /
snapshot-based prover infrastructures expose.

Usage:
  python3 scripts/replay_live.py --oracle stock|native [--jobs 4] [--limit K]
                                 [--fast] [--out corpus/mylive] [--restart-every 40]
"""
import argparse
import json
import os
import pathlib
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"
# leanprover-community/repl, built at the same toolchain as lean-toolchain:
#   git clone https://github.com/leanprover-community/repl && cd repl && lake build
# Point FARKAS_REPL_BIN at the resulting binary (default: a sibling checkout).
REPL_BIN = pathlib.Path(
    os.environ.get("FARKAS_REPL_BIN",
                   ROOT / "third_party" / "repl" / ".lake" / "build" / "bin" / "repl"))
SOLUTIONS = ROOT / "corpus" / "dsv2-download"  # from farkas-corpus acquire
NATIVE_BIN = ROOT / "oracle" / "native" / "target" / "release" / "farkas-oracled"
PRELUDE = "import Mathlib\nimport Aesop\nimport Farkas.Instrument"


class Repl:
    def __init__(self, env):
        self.proc = subprocess.Popen(
            ["lake", "env", str(REPL_BIN)],
            cwd=LEAN_DIR, env=env, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
        )

    def send(self, obj, timeout_s=1800):
        # command terminated by a blank line; response is JSON followed by blank line
        self.proc.stdin.write(json.dumps(obj) + "\n\n")
        self.proc.stdin.flush()
        buf = []
        t0 = time.monotonic()
        while True:
            if time.monotonic() - t0 > timeout_s:
                raise TimeoutError
            line = self.proc.stdout.readline()
            if line == "":
                raise EOFError("repl died")
            if line.strip() == "":
                if buf:
                    try:
                        return json.loads("".join(buf))
                    except json.JSONDecodeError:
                        continue  # blank line inside pretty-printed output
            else:
                buf.append(line)

    def close(self):
        try:
            self.proc.stdin.close()
            self.proc.wait(timeout=30)
        except Exception:
            self.proc.kill()


def strip_imports(text: str) -> str:
    return "".join(
        ln for ln in text.splitlines(keepends=True) if not ln.startswith("import ")
    )


def run_shard(worker_id, files, out_dir, oracle, fast, restart_every):
    env = os.environ | {
        "FARKAS_CORPUS_FILE": str(out_dir / f"oracle.worker{worker_id}.jsonl"),
        "FARKAS_SRC": f"worker{worker_id}",
    }
    if oracle == "native":
        env |= {"FARKAS_ORACLE": "native", "FARKAS_NATIVE_BIN": str(NATIVE_BIN)}
    if not fast:
        # fast path is on-by-default now; non-fast rows must pin it off
        env |= {"FARKAS_FAST": "0"}

    results = []
    repl, n_since_start = None, 0

    def boot():
        nonlocal repl, n_since_start
        if repl:
            repl.close()
        repl = Repl(env)
        t0 = time.monotonic_ns()
        r = repl.send({"cmd": PRELUDE})
        t1 = time.monotonic_ns()
        results.append({"ty": "import", "worker": worker_id,
                        "wallNs": t1 - t0, "err": "messages" in r and any(
                            m.get("severity") == "error" for m in r["messages"])})
        n_since_start = 0

    boot()
    for f in files:
        tag = f"{f.parent.name}/{f.name}"
        if n_since_start >= restart_every:
            boot()
        cmd = strip_imports(f.read_text())
        t0 = time.monotonic_ns()
        try:
            r = repl.send({"cmd": cmd, "env": 0})
            t1 = time.monotonic_ns()
            errs = [m for m in r.get("messages", []) if m.get("severity") == "error"]
            results.append({"ty": "file", "src": tag, "wallNs": t1 - t0,
                            "t": t0, "nErrors": len(errs),
                            "firstError": errs[0]["data"][:200] if errs else ""})
        except (TimeoutError, EOFError) as e:
            t1 = time.monotonic_ns()
            results.append({"ty": "file", "src": tag, "wallNs": t1 - t0,
                            "t": t0, "nErrors": -1, "firstError": type(e).__name__})
            boot()
        n_since_start += 1
        print(f"[w{worker_id}] {tag}: {results[-1]['nErrors']} errs "
              f"({results[-1]['wallNs'] / 1e9:.1f}s)", flush=True)
    repl.close()
    return results


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--oracle", choices=["stock", "native"], required=True)
    ap.add_argument("--fast", action="store_true",
                    help="fast path on (default: pinned off for a clean row)")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--out", type=str, default="")
    ap.add_argument("--restart-every", type=int, default=40)
    args = ap.parse_args()

    if not REPL_BIN.exists():
        sys.exit(f"REPL binary not found at {REPL_BIN} — build "
                 "leanprover-community/repl at this repo's lean-toolchain "
                 "and/or set FARKAS_REPL_BIN (see the module docstring)")
    mode = args.oracle + ("-fast" if args.fast else "")
    out_dir = pathlib.Path(args.out or str(ROOT / "corpus" / f"live-{mode}")).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    files = sorted(SOLUTIONS.glob("*/*.lean"))
    if args.limit:
        files = files[: args.limit]
    shards = [files[i::args.jobs] for i in range(args.jobs)]
    print(f"live replay ({mode}): {len(files)} theorems, "
          f"{args.jobs} live REPL workers -> {out_dir}", flush=True)

    all_results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = [pool.submit(run_shard, i, s, out_dir, args.oracle, args.fast,
                            args.restart_every)
                for i, s in enumerate(shards)]
        for fu in futs:
            all_results.extend(fu.result())

    with open(out_dir / "files.jsonl", "w") as fh:
        for r in all_results:
            fh.write(json.dumps(r) + "\n")
    ok = sum(1 for r in all_results if r["ty"] == "file" and r["nErrors"] == 0)
    nf = sum(1 for r in all_results if r["ty"] == "file")
    imp = sum(r["wallNs"] for r in all_results if r["ty"] == "import") / 1e9
    marg = sum(r["wallNs"] for r in all_results if r["ty"] == "file") / 1e9
    print(f"done: {ok}/{nf} clean; marginal(sum) {marg:.0f}s, imports(sum) {imp:.0f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
