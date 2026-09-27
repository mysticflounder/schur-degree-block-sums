"""Check the witnesses for L(4) = 16 (no SAT solver, no search).

For each witness sequence A and its listed 3-colouring:
  1. compute the block-sum set A-hat from the definition (all sums of
     consecutive entries) and check that the listed classes partition it;
  2. check that each class is sum-free: no x, y, z in the class with
     x + y = z, x = y allowed (Eliahou-Revuelta, Def. of sumfree);
  3. print the length, the sum and the average.

For the main witness W it also checks a step of the proof in the paper: for every
L in 1..15 the block of the first L entries has sum at most 4L.

Last, it builds the 3-colouring of K_16 from W (ER Thm. 4.1: vertex i is the
prefix sum p_i, edge {i, j} gets the colour of |p_i - p_j|) and checks that
no triangle is monochromatic.  It prints, for each colour, the degrees and
the numbers of common neighbours of adjacent and of non-adjacent pairs.
"""
from __future__ import annotations

from itertools import combinations

WITNESSES = {
    "W (main, sum 31)": (
        [1, 1, 1, 6, 1, 1, 1, 7, 1, 1, 1, 6, 1, 1, 1],
        [[1, 3, 8, 12, 18, 22, 28],
         [2, 6, 7, 10, 11, 25, 26, 29, 30],
         [9, 13, 16, 17, 19, 20, 21, 27, 31]],
    ),
    "W14 (sum 47)": (
        [1, 4, 1, 4, 1, 4, 1, 16, 1, 4, 1, 4, 1, 4],
        [[1, 4, 10, 16, 21, 23, 28, 36, 41, 43],
         [5, 6, 14, 15, 18, 22, 26, 38, 42, 46],
         [9, 11, 17, 27, 31, 32, 33, 37, 47]],
    ),
    "W15 (sum 60)": (
        [5, 4, 5, 4, 5, 4, 1, 4, 1, 4, 5, 4, 5, 4, 5],
        [[1, 4, 10, 19, 24, 32, 37, 46, 55, 60],
         [5, 6, 14, 15, 18, 22, 41, 42, 50, 51],
         [9, 13, 23, 27, 28, 33]],
    ),
}


def block_sums(A: list[int]) -> set[int]:
    out = set()
    for i in range(len(A)):
        s = 0
        for j in range(i, len(A)):
            s += A[j]
            out.add(s)
    return out


def sum_free(C: list[int]) -> bool:
    S = set(C)
    return not any(x + y in S for x in C for y in C if x <= y)


def check(name: str, A: list[int], classes: list[list[int]]) -> bool:
    D = block_sums(A)
    flat = [x for C in classes for x in C]
    part = len(flat) == len(set(flat)) and set(flat) == D
    free = all(sum_free(C) for C in classes)
    ok = all(a > 0 for a in A) and part and free
    print(f"{name}: length {len(A)}, sum {sum(A)}, average {sum(A) / len(A):.4f}, "
          f"|A-hat| = {len(D)}, partition {part}, sum-free {free}")
    return ok


def main() -> int:
    ok = all(check(n, A, C) for n, (A, C) in WITNESSES.items())

    A, classes = WITNESSES["W (main, sum 31)"]
    pref = [sum(A[:L]) for L in range(1, 16)]
    avg_ok = all(pref[L - 1] <= 4 * L for L in range(1, 16))
    print(f"W: sums of the first L entries, L = 1..15: {pref}; all <= 4L: {avg_ok}")
    ok = ok and avg_ok

    colour = {x: c for c, C in enumerate(classes) for x in C}
    P = [0] + [sum(A[:i]) for i in range(1, len(A) + 1)]
    col = {(i, j): colour[P[j] - P[i]] for i, j in combinations(range(16), 2)}
    mono = [t for t in combinations(range(16), 3)
            if col[t[0], t[1]] == col[t[1], t[2]] == col[t[0], t[2]]]
    print(f"K_16 from W: vertices {P}; monochromatic triangles: {len(mono)}")
    ok = ok and not mono
    for c in range(3):
        adj = {v: {w for w in range(16) if w != v and col[min(v, w), max(v, w)] == c}
               for v in range(16)}
        degs = sorted({len(adj[v]) for v in range(16)})
        lam = sorted({len(adj[v] & adj[w]) for v, w in combinations(range(16), 2) if w in adj[v]})
        mu = sorted({len(adj[v] & adj[w]) for v, w in combinations(range(16), 2) if w not in adj[v]})
        print(f"  colour {c}: degrees {degs}, common neighbours of adjacent pairs {lam}, "
              f"of non-adjacent pairs {mu}")
    print("ALL CHECKS PASS" if ok else "CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
