#!/usr/bin/env python3
"""Categorize fast-path outcomes from a replay run.

Reads ty:"fast" rows (and their probe-miss comp dumps when the run had
FARKAS_FAST_DEBUG=1) and buckets misses so each class is either fixable or
documented as principled.

Usage: python3 scripts/fast_misses.py corpus/myrun
"""

import json
import pathlib
import sys
from collections import Counter, defaultdict


def main(run_dir: str) -> int:
    run = pathlib.Path(run_dir)
    fast, tactic = [], []
    for f in run.glob("oracle.*.jsonl"):
        src = f.name
        for line in open(f):
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            r["_file"] = src
            if r["ty"] == "fast":
                fast.append(r)
            elif r["ty"] == "tactic":
                tactic.append(r)

    out = Counter(r["outcome"] for r in fast)
    n_tactic = len(tactic)
    print(f"tactic invocations: {n_tactic}, fast rows: {len(fast)}")
    for k, v in out.most_common():
        print(f"  {k:16s} {v:5d}  ({100 * v / max(1, len(fast)):.1f}% of fast rows)")
    hits = out.get("hit", 0)
    print(f"hit rate over tactic invocations: {100 * hits / max(1, n_tactic):.1f}%")
    # invocations with no fast row at all never entered the fast path
    fast_calls = {(r["_file"], r["call"]) for r in fast}
    tac_calls = {(r["_file"], r["call"]) for r in tactic}
    skipped = len(tac_calls - fast_calls)
    print(f"invocations that never entered the fast path: {skipped} "
          f"({100 * skipped / max(1, n_tactic):.1f}%)")

    # bucket probe-misses by dump shape
    buckets = defaultdict(int)
    examples = {}
    for r in fast:
        if r["outcome"] != "probe-miss":
            continue
        comps = r.get("probeComps")
        if comps is None:
            buckets["no-dump (debug off)"] += 1
            continue
        if isinstance(comps, str):
            comps = json.loads(comps)
        n_eq = sum(1 for c in comps if c[0] == "eq")
        n_hyp = len(comps)
        nnz = sum(len(c[1]) for c in comps)
        if n_hyp <= 1:
            b = "empty-probe (goal/hyps unparsed)"
        elif nnz <= n_hyp:
            b = "degenerate (all-constant comps)"
        elif n_eq * 2 >= n_hyp:
            b = "eq-heavy"
        else:
            b = "substantive (probe LP feasible)"
        buckets[b] += 1
        examples.setdefault(b, (r["_file"], r["call"]))
    if buckets:
        print("\nprobe-miss buckets:")
        for b, v in sorted(buckets.items(), key=lambda kv: -kv[1]):
            ex = examples.get(b)
            print(f"  {b:36s} {v:4d}   e.g. {ex}")

    rf = [r for r in fast if r["outcome"] == "restricted-fail"]
    if rf:
        print(f"\nrestricted-fail: {len(rf)} (nS histogram: "
              f"{Counter(r.get('nS') for r in rf)})")
        for r in rf[:10]:
            print(f"  e.g. {r['_file']} call {r['call']}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__.strip())
    sys.exit(main(sys.argv[1]))
