# The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49

This repository contains a paper by Adam McKenna (2026), its Lean 4
formalization, and the programs for its computer checks.

- Paper: [paper/schur-degree-block-sums.pdf](paper/schur-degree-block-sums.pdf)
  (source: [paper/schur-degree-block-sums.md](paper/schur-degree-block-sums.md))
- Lean library and comparator check: [lean/](lean/)
- Programs for the computer checks: [checks/](checks/)

## Results

S. Eliahou and M. P. Revuelta, *The Schur degree of additive sets*,
Discrete Math. 344(5) (2021) 112332
([doi:10.1016/j.disc.2021.112332](https://doi.org/10.1016/j.disc.2021.112332);
preprint [arXiv:2006.01502](https://arxiv.org/abs/2006.01502)), define a
number L(n) through the Schur degree of the set of block sums of a sequence
of positive integers. They prove S(n−1) + 1 ≤ L(n) ≤ R_{n−1}(3) − 1 and
S(n) ≤ n·L(n), and they conjecture L(n) = S(n−1) + 1 (their Conjecture 5.6).
The conjecture would give S(n) ≤ n(S(n−1) + 1) for the Schur numbers
(Conjecture 5.7) and S(6) ≤ 966 (Conjecture 5.8).

The paper proves:

- **L(4) = 16.** The sequence W = (1,1,1,6,1,1,1,7,1,1,1,6,1,1,1) has
  length 15 and sum 31, each prefix has average at most 4, and its 25 block
  sums are covered by three sumfree sets.
- **L(5) ≥ 49.** A lift turns a partition of the nonzero elements of
  ℤ_{m₁} × ℤ_{m₂} into n − 1 sets that are sumfree in the group into the
  bound L(n) ≥ m₁m₂. A partition of ℤ₇ × ℤ₇ gives L(5) ≥ 49. With the upper
  bound of Eliahou and Revuelta, 49 ≤ L(5) ≤ 61.

So Conjecture 5.6, which states L(4) = 14 and L(5) = 45, is false for
n = 4 and n = 5. Conjectures 5.7 and 5.8 remain open.

## Lean formalization

The library `ClassicalSchur` (Lean 4, Mathlib) proves:

| Lean theorem | Statement |
|---|---|
| `ClassicalSchur.erL_four` | L(4) = 16 |
| `ClassicalSchur.erL_five_bounds` | 49 ≤ L(5) ≤ 65 |
| `ClassicalSchur.lift_lemma` | the lift (Lemma 4.1 of the paper) |
| `ClassicalSchur.le_erL_of_groupPartition` | L(n) ≥ m₁m₂ from a group partition (Corollary 4.2) |
| `ClassicalSchur.le_sdeg_blockSums` | Theorem 4.1 of Eliahou–Revuelta, with a pigeonhole bound for R_k(3) |
| `ClassicalSchur.erL_le` | the upper bound of their Proposition 5.3, with the same bound |

The Lean upper bound for L(5) is 65, not 61: the formalization uses the
pigeonhole bound R₄(3) ≤ 66 and not the bound R₄(3) ≤ 62 of Fettes, Kramer
and Radziszowski (2004). The finite checks use the Lean kernel (`decide`),
with no native code. The only axioms are `propext`, `Classical.choice` and
`Quot.sound`.

Build (Lean v4.33.1, Mathlib as pinned in `lean/lake-manifest.json`):

```bash
cd lean
lake exe cache get
lake build
```

The six theorems are also checked with
[leanprover/comparator](https://github.com/leanprover/comparator) against a
statement file that imports only Mathlib; see
[lean/comparator/README.md](lean/comparator/README.md). The workflow
[.github/workflows/comparator.yml](.github/workflows/comparator.yml) runs
this check on each push.

## Computer checks

See [checks/README.md](checks/README.md). The programs use only the Python
standard library. The SAT checks use CaDiCaL and drat-trim.

## How to cite

A. McKenna, *The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49*,
2026. <https://github.com/mysticflounder/schur-degree-block-sums>.
See also [CITATION.cff](CITATION.cff).

## License

Apache License 2.0; see [LICENSE](LICENSE).
