"""Check the witness for L(5) >= 49 (no SAT solver, no search).

1. The four listed sets partition Z_7 x Z_7 minus 0, each is sum-free in
   the group (no g + h = k in one set, g = h allowed), and each is closed
   under negation.
2. Lift (paper, Lemma 4.1): X = {u + 19 j : 0 <= u, j <= 6}.  Every d in
   X-hat = (X - X) & N+ is d = r + 19 e with |r| <= 6, 0 <= e <= 6, and gets
   the colour of (r mod 7, e mod 7).  The script computes X-hat from the
   sequence of jumps of X (block sums, by definition), colours it, and
   checks every triple x + y = z in X-hat (x = y allowed) directly in the
   integers.
3. The first L entries of the sequence have sum at most 5L for every
   L = 1..48, and the largest average of a prefix (exact fraction) is at
   most M/7 = 19/7, as the prefix sums of Lemma 4.1 give.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product

M = 19
CLASSES = [
    [(0, 2), (0, 5), (1, 4), (2, 3), (2, 4), (3, 2), (3, 3), (4, 4), (4, 5), (5, 3), (5, 4), (6, 3)],
    [(1, 1), (1, 3), (1, 5), (1, 6), (3, 0), (3, 5), (4, 0), (4, 2), (6, 1), (6, 2), (6, 4), (6, 6)],
    [(0, 3), (0, 4), (1, 0), (1, 2), (2, 1), (2, 6), (3, 4), (4, 3), (5, 1), (5, 6), (6, 0), (6, 5)],
    [(0, 1), (0, 6), (2, 0), (2, 2), (2, 5), (3, 1), (3, 6), (4, 1), (4, 6), (5, 0), (5, 2), (5, 5)],
]


def main() -> int:
    ok = True
    G = [g for g in product(range(7), range(7)) if g != (0, 0)]
    flat = [g for C in CLASSES for g in C]
    part = len(flat) == len(set(flat)) == 48 and set(flat) == set(G)
    add = lambda a, b: ((a[0] + b[0]) % 7, (a[1] + b[1]) % 7)
    free = all(add(x, y) not in set(C) for C in CLASSES for x in C for y in C)
    neg = all(((-a) % 7, (-b) % 7) in set(C) for C in CLASSES for a, b in C)
    print(f"Z_7^2 minus 0: partition {part}, each class sum-free in the group {free}, "
          f"each class closed under negation {neg}")
    ok = ok and part and free and neg
    chi = {g: i for i, C in enumerate(CLASSES) for g in C}

    X = sorted({u + M * j for u in range(7) for j in range(7)})
    A = [X[i + 1] - X[i] for i in range(len(X) - 1)]
    D = set()
    for i in range(len(A)):
        s = 0
        for j in range(i, len(A)):
            s += A[j]
            D.add(s)
    col = {}
    for d in D:
        reps = [(r, e) for e in range(7) for r in range(-6, 7) if r + M * e == d]
        assert len(reps) == 1, d
        r, e = reps[0]
        col[d] = chi[(r % 7, e % 7)]
    bad = [(x, y) for x in D for y in D if x <= y and x + y in D and col[x] == col[y] == col[x + y]]
    print(f"A = {A}")
    print(f"length {len(A)}, sum {sum(A)}, average {sum(A) / len(A):.4f}, |A-hat| = {len(D)}, "
          f"monochromatic triples {len(bad)}")
    ok = ok and not bad and len(A) == 48
    pref = [sum(A[:L]) for L in range(1, 49)]
    avg_ok = all(pref[L - 1] <= 5 * L for L in range(1, 49))
    top = max(Fraction(p, L + 1) for L, p in enumerate(pref))
    print(f"first-L sums <= 5L for L = 1..48: {avg_ok} (largest average {top}, exact; "
          f"bound from Lemma 4.1: M/7 = {Fraction(M, 7)})")
    ok = ok and avg_ok and top <= Fraction(M, 7)
    print("ALL CHECKS PASS" if ok else "CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
