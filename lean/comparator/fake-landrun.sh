#!/usr/bin/env bash
# fake-landrun — no-sandbox dev shim for running leanprover/comparator on a
# non-Linux host (macOS).
#
# Why this exists: the comparator sandboxes each `lake build` / `lean4export`
# step with landrun (https://github.com/Zouuup/landrun), which uses the Linux
# Landlock LSM and does not run on macOS. The comparator (tag v4.33.0, built
# with this repo's lean-toolchain) invokes the sandbox by the bare name
# `landrun` found on PATH; it also supports a COMPARATOR_LANDRUN override. To run the
# comparator locally on macOS, expose THIS script as `landrun` on PATH (e.g.
# symlink it to `landrun` in a directory you prepend to PATH); it strips the
# landrun sandbox flags and execs the real command unsandboxed.
#
# This deliberately drops the sandbox, which exists to contain a MALICIOUS
# Solution author. For a self-audit of our own Solution that is not the point;
# the comparator still performs every verification leg that matters — real
# `lake build`, real `lean4export`, statement-identity comparison of the two
# exports, axiom-closure check, and a Lean default-kernel replay. The real
# `landrun` sandbox leg runs in Linux CI (.github/workflows/comparator.yml).
set -euo pipefail

# Drop known landrun flags (and their values); the first non-flag token is the
# real command. landrun arg shape (from the comparator's buildLandrunArgs):
#   --best-effort --ro / --rw /dev -ldd -add-exec [--env K]... [--ro P]...
#   [--rwx P]... [--rox P]... CMD ARGS...
while [[ $# -gt 0 ]]; do
  case "$1" in
    --best-effort|-ldd|-add-exec) shift ;;        # valueless flags
    --ro|--rw|--rwx|--rox|--env)  shift 2 ;;       # flag + one value
    --)                           shift; break ;;  # explicit end-of-flags
    -*)                           shift ;;         # unknown flag: assume valueless
    *)                            break ;;         # first non-flag token = command
  esac
done

if [[ $# -eq 0 ]]; then
  echo "fake-landrun: no command after sandbox flags" >&2
  exit 2
fi

exec "$@"
