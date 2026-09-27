"""Independent Schur-degree checker for block-sum sets (no SAT solver).

Given a sequence A of positive integers, compute the block-sum set A-hat
directly from its definition (all sums of consecutive entries), then decide
by plain backtracking whether A-hat has a partition into q sum-free parts
(sum-free: no x, y, z in one part with x + y = z, x = y allowed).

Prints the colouring found, and re-checks it triple by triple.
"""
from __future__ import annotations

import argparse
import sys


def block_sums(A: list[int]) -> list[int]:
    s = set()
    for i in range(len(A)):
        t = 0
        for j in range(i, len(A)):
            t += A[j]
            s.add(t)
    return sorted(s)


def colour(D: list[int], q: int):
    """Backtracking over D in increasing order.

    When z is coloured, every triple x + y = z with x, y < z already
    coloured is checked; this covers every triple exactly when its largest
    element is placed.  Colour symmetry: element i may use a colour at most
    one above the largest colour used so far.
    """
    Dset = set(D)
    col: dict[int, int] = {}
    order = list(D)
    # for each z, the pairs (x, y), x <= y, x + y = z, x, y in D
    pairs = {z: [(x, z - x) for x in D if x <= z - x and (z - x) in Dset] for z in D}
    sys.setrecursionlimit(10000)

    def rec(i: int, maxc: int) -> bool:
        if i == len(order):
            return True
        z = order[i]
        for c in range(min(q, maxc + 2)):
            ok = True
            for x, y in pairs[z]:
                if col[x] == c and col[y] == c:
                    ok = False
                    break
            if ok:
                col[z] = c
                if rec(i + 1, max(maxc, c)):
                    return True
                del col[z]
        return False

    return dict(col) if rec(0, -1) else None


def verify(D: list[int], col: dict[int, int], q: int) -> bool:
    Dset = set(D)
    if set(col) != Dset:
        return False
    if any(not (0 <= c < q) for c in col.values()):
        return False
    for x in D:
        for y in D:
            if x <= y and (x + y) in Dset:
                if col[x] == col[y] == col[x + y]:
                    return False
    return True


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--seq", type=str, required=True)
    args = ap.parse_args()
    A = [int(t) for t in args.seq.split(",")]
    assert all(a > 0 for a in A)
    D = block_sums(A)
    print(f"A = {A}  length {len(A)}  sum {sum(A)}  average {sum(A)/len(A):.4f}")
    print(f"|A-hat| = {len(D)}")
    col = colour(D, args.q)
    if col is None:
        print(f"no sum-free {args.q}-colouring: sdeg(A-hat) > {args.q}")
        return 1
    ok = verify(D, col, args.q)
    for c in range(args.q):
        print(f"  class {c}: {[x for x in D if col[x] == c]}")
    print(f"sum-free {args.q}-colouring found; independent triple re-check: {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 3


if __name__ == "__main__":
    raise SystemExit(main())
