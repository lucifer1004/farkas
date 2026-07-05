#!/usr/bin/env python3
"""Replay-run analysis: problem sizes, timing, and the oracle's share of
(n)linarith and end-to-end time (the numbers behind the README table).

Usage: python3 scripts/analyze.py corpus/myrun
"""
import json
import pathlib
import statistics
import sys
from collections import defaultdict


def pct(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(len(xs) * p))]


def main(run_dir: str) -> int:
    run = pathlib.Path(run_dir)
    oracle, tactic = [], []
    for f in run.glob("oracle.*.jsonl"):
        for line in open(f):
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            # rows also carry ty:"prep"/"fast" (preprocessing + fast-path
            # telemetry); this report only reads oracle and tactic rows
            if r["ty"] == "oracle":
                oracle.append(r)
            elif r["ty"] == "tactic":
                tactic.append(r)
    if not (run / "files.jsonl").exists():
        sys.exit(f"no files.jsonl in {run} — is this a replay output directory?")
    files = [json.loads(l) for l in open(run / "files.jsonl")]
    if not files:
        sys.exit(f"{run}/files.jsonl is empty")
    if not oracle:
        sys.exit(f"no oracle telemetry rows in {run} (a --stock replay "
                 "records outcomes only; instrumented runs need the daemon "
                 "or FARKAS_ORACLE unset)")

    print("=" * 64)
    print(f"REPLAY REPORT: {run}")
    print("=" * 64)

    n_ok_files = sum(1 for r in files if r["exit"] == 0)
    total_wall = sum(r["wallNs"] for r in files)
    print(f"\n## Files\n{len(files)} replayed, {n_ok_files} compiled clean "
          f"({100 * n_ok_files / len(files):.0f}%)")
    print(f"total file wall time: {total_wall / 1e9:.0f}s "
          f"(median {statistics.median(r['wallNs'] for r in files) / 1e9:.1f}s/file)")

    print(f"\n## Oracle calls\ntotal: {len(oracle)}, with certificate: "
          f"{sum(1 for r in oracle if r['ok'])} "
          f"({100 * sum(1 for r in oracle if r['ok']) / len(oracle):.1f}%)")
    kinds = defaultdict(int)
    for r in tactic:
        kinds[r["kind"], r["ok"]] += 1
    print(f"tactic invocations: {len(tactic)} "
          f"(linarith ok/fail: {kinds[('linarith', True)]}/{kinds[('linarith', False)]}, "
          f"nlinarith ok/fail: {kinds[('nlinarith', True)]}/{kinds[('nlinarith', False)]})")

    hyps = [r["nHyps"] for r in oracle]
    mv = [r["maxVar"] for r in oracle]
    nnz = [sum(len(h[1]) for h in r["hyps"]) for r in oracle]
    print(f"\n## Problem sizes (per oracle call)")
    print(f"nHyps (rows):  median {statistics.median(hyps):.0f}, "
          f"p90 {pct(hyps, 0.9)}, p99 {pct(hyps, 0.99)}, max {max(hyps)}")
    print(f"maxVar (cols): median {statistics.median(mv):.0f}, "
          f"p90 {pct(mv, 0.9)}, p99 {pct(mv, 0.99)}, max {max(mv)}")
    print(f"nnz:           median {statistics.median(nnz):.0f}, "
          f"p90 {pct(nnz, 0.9)}, p99 {pct(nnz, 0.99)}, max {max(nnz)}")

    ons = [r["ns"] for r in oracle]
    tns = [r["ns"] for r in tactic]
    print(f"\n## Timing")
    print(f"oracle ms: median {statistics.median(ons) / 1e6:.2f}, "
          f"p90 {pct(ons, 0.9) / 1e6:.1f}, p99 {pct(ons, 0.99) / 1e6:.1f}, "
          f"max {max(ons) / 1e6:.0f}")
    print(f"tactic ms: median {statistics.median(tns) / 1e6:.2f}, "
          f"p90 {pct(tns, 0.9) / 1e6:.1f}, p99 {pct(tns, 0.99) / 1e6:.1f}, "
          f"max {max(tns) / 1e6:.0f}")

    sum_o, sum_t = sum(ons), sum(tns)
    print(f"\n## Oracle share of (n)linarith time")
    print(f"sum(oracle)/sum(tactic) = {100 * sum_o / sum_t:.1f}%")
    # per-tactic-call share, weighted view
    per_call = defaultdict(lambda: [0, 0])
    for r in oracle:
        per_call[r["src"], r["call"]][0] += r["ns"]
    for r in tactic:
        per_call[r["src"], r["call"]][1] += r["ns"]
    shares = [o / t for (o, t) in per_call.values() if t > 0]
    print(f"per-tactic-call oracle share: median {100 * statistics.median(shares):.1f}%, "
          f"p90 {100 * pct(shares, 0.9):.0f}%")

    print(f"\n## (n)linarith share of file verification time")
    tac_by_src = defaultdict(int)
    for r in tactic:
        tac_by_src[r["src"]] += r["ns"]
    file_shares = []
    for r in files:
        if r["src"] in tac_by_src and r["wallNs"] > 0:
            file_shares.append(tac_by_src[r["src"]] / r["wallNs"])
    print(f"files with >=1 linarith call: {len(file_shares)}/{len(files)}")
    if file_shares:
        print(f"linarith share of file wall: median {100 * statistics.median(file_shares):.1f}%, "
              f"p90 {100 * pct(file_shares, 0.9):.0f}%, max {100 * max(file_shares):.0f}%")
    print(f"aggregate: sum(tactic)/sum(file wall) = {100 * sum_t / total_wall:.1f}%")
    print(f"aggregate: sum(oracle)/sum(file wall) = {100 * sum_o / total_wall:.1f}%")

    print(f"\n## Oracle-call arrival rate (across all replay workers)")
    ts = sorted(r["t"] for r in oracle)
    span = (ts[-1] - ts[0]) / 1e9
    rate = len(oracle) / span
    print(f"oracle calls: {len(oracle)} over {span:.0f}s => {rate:.1f} calls/s")
    for d_ms in (5, 10, 50):
        print(f"  batch@{d_ms}ms deadline: ~{rate * d_ms / 1000:.1f} calls/batch")
    # bursts: max calls in any 100ms window
    best, i = 0, 0
    for j in range(len(ts)):
        while ts[j] - ts[i] > 100e6:
            i += 1
        best = max(best, j - i + 1)
    print(f"peak 100ms window: {best} calls")
    return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__.strip())
    sys.exit(main(sys.argv[1]))
