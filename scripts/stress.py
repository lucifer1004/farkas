#!/usr/bin/env python3
"""Stress harness for the fast path + daemon under real parallel elaboration.

Lean elaborates top-level declarations in parallel, so one big generated
file with hundreds of linarith theorems exercises exactly the path the
daemon mutex protects: many concurrent request/response round-trips over
one shared child process.

Modes:
  --n N        number of generated theorems (default 300)
  --chaos      kill the daemon repeatedly during elaboration: every kill
               forces an EOF -> respawn (+ handshake) under load; the run
               must still exit 0 with every theorem closed
  --keep       keep the generated file / telemetry for inspection

Assertions: exit 0; every tactic invocation ok; zero probe-error rows;
(no-chaos only) hit rate >= 95% on this trivially-probeable distribution.

Deterministic generation (fixed LCG), mixes plain / [args] / only /
nlinarith forms and ℚ/ℤ/ℕ/generic-field types.
"""

import argparse
import json
import os
import pathlib
import random
import subprocess
import sys
import tempfile
import threading
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"


def gen(n: int, seed: int = 20260703) -> str:
    rng = random.Random(seed)
    out = ["import Mathlib", "import Farkas.Auto", ""]
    for i in range(n):
        a, b, c = rng.randint(1, 9), rng.randint(1, 9), rng.randint(1, 9)
        form = i % 6
        if form == 0:
            out.append(
                f"theorem s{i} (x y z : ℚ) (h1 : x < {a}) (h2 : y ≤ {b}) "
                f"(h3 : z ≤ x + y) : z < {a + b} := by linarith")
        elif form == 1:
            out.append(
                f"theorem s{i} (x : ℤ) (h : {c} * x ≥ {a}) : x ≥ {-(b * 7)} := by linarith")
        elif form == 2:
            out.append(
                f"theorem s{i} (n : ℕ) (h : n < {a + 1}) : n + {b} ≤ {a + b} := by linarith")
        elif form == 3:
            out.append(
                f"theorem s{i} (x y : ℚ) (h1 : x < {a}) (h2 : y < {b}) : "
                f"x + y < {a + b} := by linarith only [h1, h2]")
        elif form == 4:
            out.append(
                f"theorem s{i} (x y : ℚ) (h1 : x < {a}) (junk : y ≥ 0) (h2 : y < {b}) : "
                f"x + y < {a + b} := by linarith [h1.le]")
        else:
            out.append(
                f"theorem s{i} (u : ℝ) (hu : 0 ≤ u) : 0 ≤ u * u + {c} * u := by nlinarith")
    return "\n".join(out) + "\n"


def killer(stop: threading.Event, kills: list):
    while not stop.is_set():
        r = subprocess.run(["pkill", "-x", "farkas-oracled"], capture_output=True)
        if r.returncode == 0:
            kills.append(time.monotonic())
        stop.wait(0.4)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=300)
    ap.add_argument("--chaos", action="store_true",
                    help="repeatedly pkill farkas-oracled during the run "
                         "(NOTE: kills every farkas-oracled you own on this "
                         "machine, not just this run's)")
    ap.add_argument("--keep", action="store_true")
    args = ap.parse_args()

    tmp = pathlib.Path(tempfile.mkdtemp(prefix="farkas-stress-"))
    src = tmp / "Stress.lean"
    telemetry = tmp / "telemetry.jsonl"
    src.write_text(gen(args.n))
    env = os.environ | {"FARKAS_CORPUS_FILE": str(telemetry), "FARKAS_SRC": "stress"}

    stop, kills = threading.Event(), []
    kt = None
    if args.chaos:
        kt = threading.Thread(target=killer, args=(stop, kills), daemon=True)
        kt.start()

    t0 = time.monotonic()
    proc = subprocess.run(["lake", "env", "lean", str(src)], cwd=LEAN_DIR,
                          env=env, capture_output=True, text=True, timeout=3600)
    wall = time.monotonic() - t0
    if kt:
        stop.set()
        kt.join()

    rows = [json.loads(l) for l in open(telemetry)] if telemetry.exists() else []
    tactic = [r for r in rows if r["ty"] == "tactic"]
    fast = [r for r in rows if r["ty"] == "fast"]
    hits = sum(1 for r in fast if r["outcome"] == "hit")
    errors = sum(1 for r in fast if r["outcome"] == "probe-error")
    ok = sum(1 for r in tactic if r["ok"])

    print(f"exit={proc.returncode} wall={wall:.1f}s theorems={args.n} "
          f"tactic_ok={ok}/{len(tactic)} hits={hits} probe-errors={errors} "
          f"daemon_kills={len(kills)}")
    failed = []
    if proc.returncode != 0:
        failed.append(f"lean exited {proc.returncode}: {proc.stderr[-400:]}")
    if ok != args.n or len(tactic) != args.n:
        failed.append(f"expected {args.n} ok tactic rows, got {ok}/{len(tactic)}")
    if errors:
        failed.append(f"{errors} probe-error rows")
    if not args.chaos and hits < 0.95 * args.n:
        failed.append(f"hit rate {hits}/{args.n} below 95%")
    if args.chaos and not kills:
        failed.append("chaos mode but the killer never fired")

    if args.keep or failed:
        print(f"artifacts kept at {tmp}")
    else:
        for f in tmp.iterdir():
            f.unlink()
        tmp.rmdir()
    for f in failed:
        print(f"STRESS FAIL: {f}", file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
