# Computer checks

The programs use only the Python standard library (tested with Python
3.13).
The SAT checks use [CaDiCaL](https://github.com/arminbiere/cadical) and
[drat-trim](https://github.com/marijnheule/drat-trim). Run the commands
from this directory.

| Program | Use in the paper |
|---|---|
| `verify_L4.py` | Theorem 1.1 and Remark 3.4: no solver and no search |
| `verify_L5.py` | Theorem 1.2: no solver and no search |
| `check_sdeg.py` | a Schur-degree checker by backtracking, for any sequence |
| `exhaustive_search.c` | Remark 3.3: least sums and the uniqueness of W, with no solver |
| `ldeg_cnf.py` | the SAT formula of Remark 3.3 |
| `group_sumfree_cnf.py` | the SAT formulas of Section 5 (limits of the lift) |
| `certificates/` | the DRAT proofs of the eight UNSAT answers, compressed with xz |

## Theorem 1.1 (L(4) = 16) and Remark 3.4

```bash
python3 verify_L4.py
```

For W = (1,1,1,6,1,1,1,7,1,1,1,6,1,1,1) and two other witnesses, the
program computes the block sums from the definition, checks that the listed
classes partition them, and checks each class for sums x + y = z (x = y
included). For W it checks that the sum of the first L entries is at most
4L for L = 1, …, 15. It then builds the 3-colouring of the edges of K₁₆ of
Remark 3.4, checks that it has no monochromatic triangle, and prints the
degree and the numbers of common neighbours in each colour class. The last
line of the output is `ALL CHECKS PASS`.

## Theorem 1.2 (L(5) ≥ 49)

```bash
python3 verify_L5.py
```

The program checks that the four sets of Section 5 partition
(ℤ₇ × ℤ₇) ∖ {0}, are sumfree in the group and are closed under negation.
It builds the sequence of Lemma 4.1 with M = 19, colours its block sums by
the rule in the proof of Lemma 4.1, and checks every sum x + y = z of block
sums (x = y included) in the integers. It checks that the sum of the first
L entries is at most 5L for L = 1, …, 48. Output: length 48, sum 120, 84
block sums, no monochromatic solution, largest prefix average 19/7, and
`ALL CHECKS PASS`.

## Schur degree of a given sequence

```bash
python3 check_sdeg.py --q 3 --seq 1,1,1,6,1,1,1,7,1,1,1,6,1,1,1
```

The program decides by backtracking whether the block sums of the sequence
have a partition into q sumfree sets, and checks the partition that it
finds sum by sum.

## Remark 3.3 (least sums, and the uniqueness of W)

Exhaustive search, with no solver:

```bash
cc -O2 -o exhaustive_search exhaustive_search.c
./exhaustive_search 13 13 3     # control, S(3) = 13: 1 sequence (all entries 1)
./exhaustive_search 14 14 3     # control: 0 sequences
./exhaustive_search 14 29 3     # 0 sequences
./exhaustive_search 14 30 3     # 6 sequences
./exhaustive_search 15 31 3     # 1 sequence: 1 1 1 6 1 1 1 7 1 1 1 6 1 1 1 (W)
```

The arguments are the length L, the largest sum S and the number Q of
sumfree sets. The program counts the sequences of L positive integers with
sum at most S whose block sums are covered by Q sumfree sets; the header of
`exhaustive_search.c` explains the search. On the machine used for the
paper, each of the last three runs took less than one minute.

SAT formula for the length-14 bound, with its DRAT proof:

```bash
python3 ldeg_cnf.py --q 3 --L 14 --sigma 29 -o r33.cnf
cadical r33.cnf r33.drat        # s UNSATISFIABLE
drat-trim r33.cnf r33.drat      # s VERIFIED
```

The formula asks for a sequence of 14 positive integers with sum at most 29
whose block sums have Schur degree at most 3. The header of `ldeg_cnf.py`
describes the encoding. SHA-256 of the formula:
`dbe0be928cf7bdd34520fa618ce02fb66f77367cb05eafe924e10276d2a49228`.

## Section 5 (the limits of the lift at n = 5)

For each non-cyclic abelian group G of order 50 to 60, the formula asks for
a cover of G ∖ {0} by 4 sets that are sumfree in G (`--sb` fixes the colours
of one element t and of 2t; the header of `group_sumfree_cnf.py` shows why
this is sound):

```bash
python3 group_sumfree_cnf.py 4 2x26 --sb > g.cnf
shasum -a 256 g.cnf
cadical g.cnf g.drat            # s UNSATISFIABLE
drat-trim g.cnf g.drat          # s VERIFIED
```

The output is sorted, so the formula is the same on each run. First 16 hex
digits of the SHA-256 digest of each formula:

| group | variables / clauses | SHA-256 (first 16 hex digits) |
|---|---|---|
| ℤ₂×ℤ₂₆ | 204 / 4,953 | 131c269b0241f63e |
| ℤ₃×ℤ₁₈ | 212 / 5,551 | 3807221cee343ff5 |
| ℤ₃×ℤ₃×ℤ₆ | 212 / 5,515 | 02eb4eaf94a9fbfc |
| ℤ₂×ℤ₂₈ | 220 / 5,781 | 2a024113bbda0374 |
| ℤ₂×ℤ₂×ℤ₁₄ | 220 / 5,365 | 61b562b05d3190b2 |
| ℤ₅×ℤ₁₀ | 196 / 4,755 | 95fd109febacfb81 |
| ℤ₂×ℤ₃₀ | 236 / 6,669 | 441c39577654b62a |

The group arguments are `2x26`, `3x18`, `3x3x6`, `2x28`, `2x2x14`, `5x10`
and `2x30`. Full SHA-256 digests of the formulas:

```
131c269b0241f63e4b2e5a93117d57e69323a427f601d8dea24ec4f4213c09d0  2x26
3807221cee343ff5794ea97b5fae1e4e192947540398111a00e000a851eace48  3x18
02eb4eaf94a9fbfc415a08d1606f8b784a8bf247d29cc271c067b2403f90dcd3  3x3x6
2a024113bbda0374e3317c3b2d9585c88b968733724b26eacb94e2b16921c111  2x28
61b562b05d3190b2990b80da1908f5295380e2fe1028b5ab8f53814cf219395d  2x2x14
95fd109febacfb815a8ec97277bc45c314005699c22696fb9fa17398208b5f56  5x10
441c39577654b62ad1db6bad47faf9e9dd7e89ed11d704a9a05ea22c4975b0dc  2x30
```

## Certificates

`certificates/` holds the DRAT proofs of the eight UNSAT answers (Remark 3.3
and the seven groups of Section 5), in CaDiCaL's binary DRAT format,
compressed with xz. They were made with CaDiCaL 3.0.0 and checked with
drat-trim (a local build of https://github.com/marijnheule/drat-trim; the
SHA-256 of the binary is in the log). To check one proof:

```bash
python3 group_sumfree_cnf.py 4 5x10 --sb > g5x10.cnf
xz -dk certificates/g5x10.drat.xz
drat-trim g5x10.cnf certificates/g5x10.drat     # s VERIFIED
```

`certificates/verification-log.txt` gives, for each formula, its first
line, its SHA-256 digest, the solver answer, the drat-trim answer, and the
size and SHA-256 digest of the uncompressed proof.
`certificates/SHA256SUMS-xz.txt` gives the digests of the compressed files.

## Not in this directory

The isomorphism test of Remark 3.4 and the solver searches of Section 6
were made with programs that are not in this repository.
