#!/usr/bin/env bash
# Runs the `lake comparator` of this project's own toolchain
# (lean/lean-toolchain) on comparator/config.json. It checks, for each theorem
# that config.json lists:
#
#   1. statement identity between ClassicalChallenge and ClassicalSolution,
#      with every definition that the statement uses;
#   2. axiom compliance: the axioms are in config.json's permitted_axioms;
#   3. kernel acceptance by Lean's kernel and by the independent kernels
#      nanoda (nanoda_bin) and con-ron that the toolchain bundles.
#
# Nothing that judges is built from a pin: lake comparator, leanexport and the
# kernels all come from lean/lean-toolchain (Lean v4.35.0-rc2 or later).
# lake comparator builds and exports the project in a bubblewrap (bwrap)
# sandbox, so this script needs Linux with bwrap. The workflow
# .github/workflows/comparator.yml runs it.
#
# Exits 0 only when lake comparator accepts the solution.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"             # the lean/ directory
cd "$LEAN_ROOT"

CONFIG=comparator/config.json

for required_command in bwrap jq lake lean; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain="$(tr -d '[:space:]' < lean-toolchain)"
prefix="$(lean --print-prefix)"
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [[ ! -x "$prefix/bin/$tool" ]]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "lake comparator with bundled kernels needs leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

# A generated copy of config.json: the same theorem_names and permitted_axioms;
# enable_nanoda is replaced by external_kernels that name the toolchain's
# bundled nanoda and con-ron binaries.
config="$(mktemp "${TMPDIR:-/tmp}/classical-comparator-config.XXXXXX")"
trap 'rm -f "$config"' EXIT
jq --arg prefix "$prefix" '
  del(.enable_nanoda)
  | .external_kernels = {
      "nanoda": [($prefix + "/bin/nanoda_bin")],
      "con-ron": [($prefix + "/bin/con-ron")]
    }' "$CONFIG" >"$config"

echo "== lake comparator ($toolchain) =="
cat "$config"
lake exe cache get
lake comparator --config "$config"
