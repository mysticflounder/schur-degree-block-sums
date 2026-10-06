#!/usr/bin/env bash
# Offline pre-flight for the comparator package. It does NOT
# replace a `lake comparator` run (statement identity, axiom compliance,
# replay by the Lean kernel, nanoda and con-ron; see README.md,
# verify-comparator.sh and .github/workflows/comparator.yml). It checks:
#
#   1. ClassicalChallenge (Mathlib only, `sorry` stubs) and ClassicalSolution
#      (proofs from the ClassicalSchur library) build.
#   2. axiom-audit.lean has one `#print axioms` line for each theorem in
#      config.json, and each reported closure is a subset of
#      {propext, Classical.choice, Quot.sound}. Any other output line fails.
#
# Exits 0 only when both checks pass.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"             # the lean/ directory
cd "$LEAN_ROOT"

AUDIT=comparator/axiom-audit.lean
CONFIG=comparator/config.json

echo "== the audit lists exactly the configured theorems =="
diff <(jq -r '.theorem_names[]' "$CONFIG" | sort) \
     <(grep -F '#print axioms ' "$AUDIT" | cut -d' ' -f3 | sort) || {
  echo "FAIL: $AUDIT and $CONFIG list different theorems" >&2
  exit 1
}
NAMES="$(jq -r '.theorem_names | length' "$CONFIG")"

echo "== building ClassicalChallenge / ClassicalSolution =="
lake build ClassicalChallenge ClassicalSolution

echo "== axiom audit =="
OUT="$(mktemp "${TMPDIR:-/tmp}/classical-comparator-audit.XXXXXX")"
trap 'rm -f "$OUT"' EXIT
lake env lean "$AUDIT" >"$OUT" 2>&1 || {
  echo "FAIL: $AUDIT did not elaborate" >&2
  cat "$OUT" >&2
  exit 1
}

fail=0
got=0
while IFS= read -r line; do
  [[ -z "$line" ]] && continue
  if [[ "$line" == *" does not depend on any axioms" ]]; then
    got=$((got + 1))
    continue
  fi
  if [[ "$line" != *" depends on axioms: ["*"]" ]]; then
    echo "FAIL: unexpected audit output: $line" >&2
    fail=1
    continue
  fi
  got=$((got + 1))
  list="${line#* depends on axioms: [}"
  list="${list%]}"
  IFS=',' read -ra axioms <<<"$list"
  for ax in "${axioms[@]}"; do
    ax="${ax# }"
    case "$ax" in
      propext|Classical.choice|Quot.sound) ;;
      *) echo "FAIL: axiom not permitted: $ax in: $line" >&2; fail=1 ;;
    esac
  done
done <"$OUT"

if [[ "$got" -ne "$NAMES" ]]; then
  echo "FAIL: expected $NAMES axiom reports, got $got" >&2
  fail=1
fi
if [[ "$fail" -ne 0 ]]; then
  cat "$OUT" >&2
  exit 1
fi

cat "$OUT"
echo "OK: $NAMES theorems build; each axiom closure is a subset of"
echo "    {propext, Classical.choice, Quot.sound}. Statement identity with"
echo "    ClassicalChallenge is checked by lake comparator (verify-comparator.sh)."
