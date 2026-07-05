#!/usr/bin/env python3
"""Validate the certificate-LP spec interpretation against the corpus.

Interpretation under test (see docs/certificate-lp-spec.md):

A corpus row's `hyps` is the exact `List Comp` passed to
`CertificateOracle.produceCertificate` (Mathlib.Tactic.Linarith), i.e. AFTER
proveFalseByLinarith has (a) prepended a proof of `-1 < 0` and (b) inserted a
negated copy of every equality hypothesis (Verification.lean:204-209,152-162).

Atom index 0 is the constant monomial `1` (Datatypes.lean:125; guaranteed
because `-1 < 0` is the first expression parsed, so the constant monomial is
the first monomial interned by elimMonom, Parsing.lean:203-210).

A certificate {i -> c_i} (c_i : Nat, c_i > 0) is VALID iff
  (1) for EVERY atom a in 0..maxVar (constant atom 0 included):
        sum_i c_i * coeff_i(a) == 0            [Frontend.lean:43, ring check
                                                Verification.lean:246]
  (2) Ineq.max over {str_i : i in cert} == lt, i.e. at least one hyp with a
      positive coefficient is strict            [Ineq.lean:38-43,
                                                Comp.isContr Datatypes.lean:171,
                                                strict objective
                                                PositiveVector.lean:50,
                                                SimplexAlgorithm.lean:67]

This is exactly `Comp.isContr` of the Nat-weighted sum of the hyps.

The script also cross-checks structural invariants used by the LP reduction:
  - hyps[0] == ("lt", [[0,-1]])  (the injected -1 < 0)
  - every "eq" hyp has its negation present among the hyps (so lambda >= 0
    suffices; equalities never need negative multipliers)
"""

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

_ap = argparse.ArgumentParser(description=__doc__)
_ap.add_argument("--corpus", required=True, help="directory of oracle.*.jsonl files")
CORPUS = Path(_ap.parse_args().corpus)


def validate_cert(hyps, cert, max_var):
    """Return (ok, reason). hyps: list of (str, [(atom, coeff), ...])."""
    if not cert:
        return False, "empty certificate"
    acc = defaultdict(int)  # atom -> weighted coefficient sum
    strict_used = False
    for idx, c in cert:
        if not (isinstance(c, int) and c > 0):
            return False, f"non-positive Nat coeff {c} at hyp {idx}"
        if not (0 <= idx < len(hyps)):
            return False, f"hyp index {idx} out of range"
        s, linexp = hyps[idx]
        if s == "lt":
            strict_used = True
        for atom, coeff in linexp:
            if not (0 <= atom <= max_var):
                return False, f"atom {atom} out of range (maxVar={max_var})"
            acc[atom] += c * coeff
    nonzero = {a: v for a, v in acc.items() if v != 0}
    if nonzero:
        return False, f"weighted sum not identically zero: {nonzero}"
    if not strict_used:
        return False, "no strict (lt) hypothesis has positive coefficient"
    return True, ""


def main():
    files = sorted(CORPUS.glob("oracle.*.jsonl"))
    n_oracle = 0
    n_with_cert = 0
    n_valid = 0
    failures = []
    # structural invariants
    bad_hyp0 = 0
    eq_without_negation = 0
    certs_using_hyp0 = 0
    all_le_after_drop_h0 = 0

    for f in files:
        with open(f) as fh:
            for lineno, line in enumerate(fh, 1):
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                if row.get("ty") != "oracle":
                    continue
                n_oracle += 1
                hyps = [(h[0], [(a, c) for a, c in h[1]]) for h in row["hyps"]]

                # invariant: hyp 0 is the injected -1 < 0
                if not hyps or hyps[0] != ("lt", [(0, -1)]):
                    bad_hyp0 += 1

                # invariant: every eq hyp has its negation among the hyps
                linexp_set = {(s, tuple(sorted(le))) for s, le in hyps}
                for s, le in hyps:
                    if s == "eq":
                        neg = ("eq", tuple(sorted((a, -c) for a, c in le)))
                        if neg not in linexp_set:
                            eq_without_negation += 1
                            break

                if row.get("cert") is None:
                    continue
                n_with_cert += 1
                cert = [(i, c) for i, c in row["cert"]]
                ok, reason = validate_cert(hyps, cert, row["maxVar"])
                if ok:
                    n_valid += 1
                    if any(i == 0 for i, _ in cert):
                        certs_using_hyp0 += 1
                    if all(hyps[i][0] != "lt" for i, _ in cert if i != 0):
                        all_le_after_drop_h0 += 1
                else:
                    failures.append(
                        {"file": f.name, "line": lineno, "call": row.get("call"),
                         "src": row.get("src"), "reason": reason, "cert": row["cert"]})

    print(f"oracle rows:                 {n_oracle}")
    print(f"rows with certificate:       {n_with_cert}")
    print(f"certificates valid:          {n_valid}")
    pct = 100.0 * n_valid / n_with_cert if n_with_cert else 0.0
    print(f"validation rate:             {pct:.4f}%")
    print()
    print("structural invariants:")
    print(f"  rows whose hyps[0] != ('lt', [[0,-1]]):    {bad_hyp0}")
    print(f"  rows with an eq hyp lacking its negation:  {eq_without_negation}")
    print(f"  valid certs using hyp 0 (-1 < 0):          {certs_using_hyp0}")
    print(f"  valid certs whose only lt-hyp is hyp 0:    {all_le_after_drop_h0}")
    if failures:
        print(f"\nFAILURES ({len(failures)}):")
        for x in failures[:50]:
            print(f"  {x['file']}:{x['line']} call={x['call']} {x['reason']} cert={x['cert']}")
    return 0 if n_with_cert and pct >= 99.9 else 1


if __name__ == "__main__":
    sys.exit(main())
