# Comparator check

This directory checks the six main theorems of the `ClassicalSchur` library
with `lake comparator`, the comparator that the Lean toolchain of
`../lean-toolchain` bundles.

| File | Content |
|---|---|
| `ClassicalChallenge.lean` | Imports Mathlib only. The definitions (`SumFree`, `CoveredBySumFree`, `sdeg`, `blockSums`, `average`, `ERProperty`, `erL`, `ramseyBound`, `GroupSumFree`, `liftPrefix`, `liftSeq`) and the six statements with `sorry`, in the namespace `ClassicalSchurClaims`. A reviewer reads this file. |
| `ClassicalSolution.lean` | Imports `ClassicalSchur`. The same definitions, word for word, and a proof of each statement by the library theorem of the same name. |
| `config.json` | The six theorem names, the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`) and `enable_nanoda: true`. |
| `axiom-audit.lean` | `#print axioms` for each of the six theorems. |
| `check-conformance.sh` | Builds both modules, checks that the audit lists the configured theorems, and checks each axiom closure against the three permitted axioms. |
| `verify-comparator.sh` | Runs `lake comparator` on a copy of `config.json` in which the kernels nanoda and con-ron of the toolchain replace `enable_nanoda`. |

## The six theorems

| `ClassicalSchurClaims.` | Statement |
|---|---|
| `erL_four` | `erL 4 = 16` |
| `erL_five_bounds` | `49 ≤ erL 5 ∧ erL 5 ≤ 65` |
| `le_erL_of_groupPartition` | a cover of the nonzero elements of `ZMod m₁ × ZMod m₂` by `n − 1` sets that are sumfree in the group gives `m₁ * m₂ ≤ erL n` (n ≥ 3) |
| `lift_lemma` | the lift `liftSeq m₁ m₂ M`: its length, positive entries, Schur degree of its block sums at most `q`, and prefix sums |
| `le_sdeg_blockSums` | Theorem 4.1 of Eliahou–Revuelta for sequences of natural numbers, with the pigeonhole bound `ramseyBound k` in place of `R_k(3)` |
| `erL_le` | `erL (k + 1) ≤ ramseyBound k - 1` (their Proposition 5.3, with the same bound) |

The deliberate differences from the definitions of Eliahou and Revuelta are
listed in the module docstring of `ClassicalChallenge.lean`: the ambient set
is ℕ, `erL n` is defined for every `n`, the average of the empty sequence is
0, and `ramseyBound k` (with `ramseyBound 0 = 2` and
`ramseyBound (k + 1) = (k + 1) * (ramseyBound k - 1) + 2`) replaces `R_k(3)`.

## How the definitions are checked

The comparator compares every constant that a configured statement uses,
transitively, between the two exports: name, type and value. So the
definitions in `ClassicalChallenge.lean` must be the same constants as the
ones in `ClassicalSolution.lean`. The proofs in `ClassicalSolution.lean` use
the library theorems, so the kernel must unfold each `ClassicalSchurClaims`
definition to the `ClassicalSchur` definition of the same name. For
`ramseyBound` (a structural recursion) a private induction lemma does this.
A change to a definition in `ClassicalChallenge.lean` alone makes the run
fail with `Const does not match between challenge and target`. All Lean files
use the module system; the definitions of both files are in an
`@[expose] public section`, so that their values are exported.

## Run it

Pre-flight, from the repository root:

```bash
lean/comparator/check-conformance.sh
```

Comparator, from the repository root, on Linux with
[bubblewrap](https://github.com/containers/bubblewrap) (`bwrap`) and `jq`:

```bash
lean/comparator/verify-comparator.sh
```

The script checks that the toolchain of `../lean-toolchain` bundles
`lake comparator`, `leanexport`, `leanchecker`, `nanoda_bin` and `con-ron`.
It writes a copy of `config.json` with the same theorem names and permitted
axioms, in which `external_kernels` names the toolchain's `nanoda_bin` and
`con-ron` in place of `enable_nanoda`. Then it runs, from `lean/`,

```bash
lake exe cache get
lake comparator --config <the copy>
```

`lake comparator` builds and exports `ClassicalChallenge` and
`ClassicalSolution` in its `bwrap` sandbox, compares the statements, checks
the axioms, and replays the proofs with the Lean kernel, nanoda and con-ron.
It exits with status 0 and prints "Your solution is okay!" when it accepts
the solution. Nothing that judges is built from a
pin: every tool comes from the toolchain. The workflow
[`../../.github/workflows/comparator.yml`](../../.github/workflows/comparator.yml)
runs the pre-flight and this script.
