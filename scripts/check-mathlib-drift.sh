#!/usr/bin/env bash
# Drift alarm: the fast path copies the two stock linarith elab bodies
# (Instrument.lean) and mirrors preprocessing semantics (Fast.lean). Those
# copies are only correct for the exact Mathlib sources they were derived
# from, so this check pins the relevant files by hash and fails when they
# change — forcing a *reviewed* re-sync instead of a silent divergence.
#
# On failure:
#   1. diff the changed file(s) against the pinned Mathlib rev;
#   2. re-verify Instrument.lean elab bodies and Fast.lean semantics
#      (eq mirroring, ℕ strictness shift, cast distribution, ...);
#   3. re-run the differential replay (behavior must stay bit-identical);
#   4. regenerate the baseline:  $0 --update
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BASELINE="$ROOT/lean/mathlib-drift.sha256"
MATHLIB="$ROOT/lean/.lake/packages/mathlib"

if [ ! -d "$MATHLIB" ]; then
  echo "ERROR: $MATHLIB not found — run 'lake build' (or 'lake update') first" >&2
  exit 2
fi

WATCHED=(
  Mathlib/Tactic/Linarith/Frontend.lean
  Mathlib/Tactic/Linarith/Preprocessing.lean
  Mathlib/Tactic/Linarith/Verification.lean
  Mathlib/Tactic/Linarith/Datatypes.lean
)

sha256() {  # GNU sha256sum or BSD/macOS shasum
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$@"
  else shasum -a 256 "$@"; fi
}

current() {
  (cd "$MATHLIB" && sha256 "${WATCHED[@]}")
}

if [ "${1:-}" = "--update" ]; then
  current > "$BASELINE"
  echo "baseline updated: $BASELINE"
  exit 0
fi

if ! current | diff -u "$BASELINE" - ; then
  cat >&2 <<'EOF'
ERROR: watched Mathlib linarith sources changed upstream.
The fast path mirrors their semantics; review the diff, re-sync
Farkas/{Instrument,Fast}.lean if needed, re-run the differential replay,
then refresh the baseline with:  scripts/check-mathlib-drift.sh --update
EOF
  exit 1
fi
echo "mathlib drift check OK (${#WATCHED[@]} files unchanged)"
