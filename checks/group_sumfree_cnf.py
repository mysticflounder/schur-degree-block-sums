"""CNF: partition of G minus 0 into q sets, each sum-free in G.

G = Z_n1 x ... x Z_nr, given as "n1xn2x...".  A set C is sum-free in G if
there are no g, h, k in C with g + h = k in G (g = h allowed).  Used for
Lemma 4.1 / Corollary 4.2 of the paper.

Variables: c(g, j), g in G minus 0 (in the order of itertools.product),
j in [0, q): g may take colour j.
Clauses:  each g takes a colour; for g, h (g = h allowed) with g + h != 0,
not all of g, h, g + h take colour j.  A solution gives a cover by q
sum-free sets; a partition follows by keeping one colour per element.
--sym:    c(-g, j) whenever c(g, j).
--sb:     colour(t) = 0 and colour(2t) = 1 for the first t with 2t != 0.
          Sound: t, t, 2t is a forbidden triple, so t and 2t have different
          colours, and the colours can be renamed.  If every nonzero
          element has order 2, or q = 1, only one colour is fixed.
Output is sorted, so the file is the same on every run.
"""
import argparse
import itertools
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("q", type=int)
    ap.add_argument("group", help='for example "7x7" or "2x2x14"')
    ap.add_argument("--sym", action="store_true")
    ap.add_argument("--sb", action="store_true")
    a = ap.parse_args()
    q, ns = a.q, [int(t) for t in a.group.split("x")]
    E = [e for e in itertools.product(*[range(n) for n in ns]) if any(e)]
    idx = {e: i for i, e in enumerate(E)}
    v = lambda e, c: idx[e] * q + c + 1
    add = lambda g, h: tuple((x + y) % n for x, y, n in zip(g, h, ns))
    cl = set()
    for e in E:
        cl.add(tuple(v(e, c) for c in range(q)))
        if a.sym:
            ne = tuple((-x) % n for x, n in zip(e, ns))
            for c in range(q):
                cl.add((-v(e, c), v(ne, c)))
    for i, g in enumerate(E):
        for h in E[i:]:
            k = add(g, h)
            if not any(k):
                continue
            for c in range(q):
                cl.add(tuple(sorted({-v(g, c), -v(h, c), -v(k, c)})))
    if a.sb:
        t = next((e for e in E if any(add(e, e))), None)
        if t is None or q < 2:  # all of order 2, or one colour: fix one only
            cl.add((v(t if t is not None else E[0], 0),))
        else:
            cl.add((v(t, 0),))
            cl.add((v(add(t, t), 1),))
    out = sys.stdout
    out.write(f"c sum-free partition q={q} G=Z_{a.group} sym={a.sym} sb={a.sb}\n")
    out.write(f"p cnf {len(E) * q} {len(cl)}\n")
    for c in sorted(cl):
        out.write(" ".join(map(str, c)) + " 0\n")


if __name__ == "__main__":
    main()
