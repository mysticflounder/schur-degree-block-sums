"""CNF for the Eliahou-Revuelta quantity L(n) (arXiv:2006.01502, Def. 5.1).

Question encoded, for q colours, length L and span bound SIGMA:

    Is there a set X of integers with 0 in X, X subset [0, SIGMA], |X| >= L + 1,
    such that the positive difference set D = (X - X) & [1, SIGMA] has a
    q-colouring in which no colour class contains a, b, a + b (a = b allowed)?

X is the prefix-sum set {0, p_1, ..., p_L} of a sequence A of positive
integers, and D is the block-sum set A-hat (ER Prop. 2.7).  A set with more
than L + 1 points contains L + 1 consecutive points, whose block has sum at
most SIGMA; block sums of a block are block sums of A (ER Prop. 2.5), and the
Schur degree is monotone under inclusion (ER Lemma 3.1).  So "at least L + 1"
and "exactly L + 1" give the same answer.

Hence UNSAT at (q, L, SIGMA) = (n - 1, L, n * L) proves L(n) <= L, and with
L = S(n - 1) + 1 it proves ER Conjecture 5.6 at n, which gives
S(n) <= n (S(n - 1) + 1) by ER Theorem 5.4.

Variables
  x(v)    v in [0, SIGMA]      v is in X
  d(v)    v in [1, SIGMA]      v is forced into D
  c(v, j) v in [1, SIGMA]      v may take colour j
Clauses
  x(0)
  -x(u) | -x(w) | d(w - u)                 for u < w
  -d(v) | c(v, 0) | ... | c(v, q - 1)
  -c(a, j) | -c(b, j) | -c(a + b, j)       for a <= b, a + b <= SIGMA
  at least L + 1 of the x(v)               (Sinz sequential counter)

d(v) is only forced upward.  Setting extra d(v) true only adds colouring
demands, so any model restricts to a proper colouring of the true D, and
the true D gives a model.  Colour classes need not be disjoint; any model
yields a proper colouring by picking one true colour per element, because
every Schur clause is negative.

Optional fixed X (for oracle checks): the x(v) are fixed by unit clauses and
the counter is omitted.
"""
from __future__ import annotations

import argparse
import sys


class Cnf:
    def __init__(self) -> None:
        self.nvars = 0
        self.clauses: list[list[int]] = []

    def new(self) -> int:
        self.nvars += 1
        return self.nvars

    def add(self, cl: list[int]) -> None:
        self.clauses.append(cl)

    def write(self, out, comments: list[str]) -> None:
        for line in comments:
            out.write(f"c {line}\n")
        out.write(f"p cnf {self.nvars} {len(self.clauses)}\n")
        for cl in self.clauses:
            out.write(" ".join(map(str, cl)) + " 0\n")


def at_least(cnf: Cnf, lits: list[int], k: int) -> None:
    """Sinz sequential counter: at least k of lits are true.

    s[i][j] (j = 1..k) means: among lits[0..i], at least j are true.
    s[i][j] -> s[i-1][j] | lits[i]
    s[i][j] -> s[i-1][j] | s[i-1][j-1]      (j >= 2)
    s[i][1] -> s[i-1][1] | lits[i]          (covered by the first rule)
    s[0][1] -> lits[0];  s[0][j] false for j >= 2.
    Require s[N-1][k].
    """
    n = len(lits)
    if k <= 0:
        return
    if k > n:
        cnf.add([])
        return
    prev = [None] * (k + 1)
    for i, lit in enumerate(lits):
        cur = [None] * (k + 1)
        for j in range(1, min(k, i + 1) + 1):
            s = cnf.new()
            cur[j] = s
            # s -> prev[j] | lit
            cl = [-s, lit]
            if prev[j] is not None:
                cl.append(prev[j])
            cnf.add(cl)
            if j >= 2:
                # s -> prev[j] | prev[j-1]
                cl = [-s]
                if prev[j] is not None:
                    cl.append(prev[j])
                if prev[j - 1] is not None:
                    cl.append(prev[j - 1])
                cnf.add(cl)
        prev = cur
    cnf.add([prev[k]])


def build(q: int, L: int, sigma: int, fixed_x: list[int] | None = None,
          pal: int | None = None):
    cnf = Cnf()
    x = {v: cnf.new() for v in range(0, sigma + 1)}
    d = {v: cnf.new() for v in range(1, sigma + 1)}
    c = {(v, j): cnf.new() for v in range(1, sigma + 1) for j in range(q)}
    cnf.add([x[0]])
    for u in range(0, sigma + 1):
        for w in range(u + 1, sigma + 1):
            cnf.add([-x[u], -x[w], d[w - u]])
    for v in range(1, sigma + 1):
        cnf.add([-d[v]] + [c[(v, j)] for j in range(q)])
    for a in range(1, sigma + 1):
        for b in range(a, sigma + 1 - a):
            for j in range(q):
                if a == b:
                    cnf.add([-c[(a, j)], -c[(2 * a, j)]])
                else:
                    cnf.add([-c[(a, j)], -c[(b, j)], -c[(a + b, j)]])
    if fixed_x is not None:
        fx = set(fixed_x)
        for v in range(0, sigma + 1):
            cnf.add([x[v]] if v in fx else [-x[v]])
    else:
        at_least(cnf, [x[v] for v in range(0, sigma + 1)], L + 1)
    if pal is not None:
        # restriction (for witness search only): max X = pal and X = pal - X
        cnf.add([x[pal]])
        for v in range(pal + 1, sigma + 1):
            cnf.add([-x[v]])
        for v in range(0, pal + 1):
            cnf.add([-x[v], x[pal - v]])
    return cnf, x, d, c


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True, help="colours for D")
    ap.add_argument("--L", type=int, required=True, help="sequence length")
    ap.add_argument("--sigma", type=int, required=True, help="max sum")
    ap.add_argument("--seq", type=str, default=None,
                    help="fix the sequence A (comma separated); sigma must be >= sum")
    ap.add_argument("--pal", type=int, default=None,
                    help="restrict to X symmetric with max X = PAL (witness search only)")
    ap.add_argument("-o", "--out", type=str, default="-")
    args = ap.parse_args()
    fixed = None
    if args.seq:
        seq = [int(t) for t in args.seq.split(",")]
        p = [0]
        for a in seq:
            p.append(p[-1] + a)
        if p[-1] > args.sigma:
            print("sum exceeds sigma", file=sys.stderr)
            return 2
        fixed = p
    cnf, *_ = build(args.q, args.L, args.sigma, fixed, args.pal)
    comments = [f"ldeg q={args.q} L={args.L} sigma={args.sigma} seq={args.seq} pal={args.pal}"]
    if args.out == "-":
        cnf.write(sys.stdout, comments)
    else:
        with open(args.out, "w") as f:
            cnf.write(f, comments)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
