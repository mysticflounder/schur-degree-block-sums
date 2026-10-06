---
title: "The Schur degree of block sums: $L(4)=16$ and $L(5)\\ge 49$"
title-meta: "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49"
author: Adam McKenna
date: "September 2026. doi:10.5281/zenodo.22987189"
abstract: |
  Eliahou and Revuelta defined a number $L(n)$ through the Schur degree of
  the set of block sums of a sequence of positive integers. They proved
  $S(n-1)+1\le L(n)\le R_{n-1}(3)-1$ and $S(n)\le n\,L(n)$, and they
  conjectured $L(n)=S(n-1)+1$, which would give the recursive bound
  $S(n)\le n\,(S(n-1)+1)$ for the Schur numbers and $S(6)\le 966$. For
  $n=4$ they proved $14\le L(4)\le 16$ and left the value open. We prove
  $L(4)=16$ with one sequence of length 15 and an explicit partition of its
  25 block sums into three sumfree sets. We then give a lift that turns a
  partition of the nonzero elements of $\mathbb{Z}_{m_1}\times\mathbb{Z}_{m_2}$
  into $n-1$ sets that are sumfree in the group into the lower bound
  $L(n)\ge m_1m_2$. A partition of $\mathbb{Z}_7\times\mathbb{Z}_7$ gives
  $L(5)\ge 49$. So the conjecture is false for $n=4$ and $n=5$. The two
  recursive consequences, Conjectures 5.7 and 5.8, remain open. The value $L(4)=16$, the bound
  $L(5)\ge49$ and the lift are also formalized in Lean 4 with Mathlib.
---

# 1. Introduction

A set $S$ of integers is *sumfree* when there are no $x,y,z\in S$ with
$x+y=z$; the elements $x$ and $y$ may be equal. The Schur number $S(n)$ is
the largest $N$ such that $\{1,\dots,N\}$ is the union of $n$ sumfree sets.
Only $S(1),\dots,S(5)=1,4,13,44,160$ are known; $S(4)=44$ is due to Baumert
[Bau61] and $S(5)=160$ to Heule [Heu18]. For $S(6)$, Eliahou and Revuelta
give the range $536\le S(6)\le 1836$ [ER21]; the lower bound is due to
Fredricksen and Sweet [FS00].

Eliahou and Revuelta [ER21] introduced the *Schur degree* $\operatorname{sdeg}(X)$
of a set $X$: the least number of sumfree sets that cover $X$. They applied
it to the set $\hat A$ of block sums of a finite sequence $A$ of positive
integers, and they defined $L(n)$ as the least length $L$ such that every
sequence of $L$ positive integers with average at most $n$ has
$\operatorname{sdeg}(\hat A)\ge n$ (Section 2). They proved

$$S(n-1)+1\le L(n)\le R_{n-1}(3)-1 \qquad\text{and}\qquad S(n)\le n\,L(n),$$

where $R_k(3)$ is the Ramsey number of the triangle in $k$ colours, and
they stated three conjectures:

- Conjecture 5.6: $L(n)=S(n-1)+1$ for $n\ge 2$;
- Conjecture 5.7: $S(n)\le n\,(S(n-1)+1)$;
- Conjecture 5.8: $S(6)\le 966$.

Conjecture 5.6 implies the other two. The two bounds on $L(n)$ agree for
$n=2$ and $n=3$, which gives $L(2)=2$ and $L(3)=5$. For $n=4$ they give
$14\le L(4)\le 16$. Eliahou and Revuelta conjectured $L(4)=14$, asked
whether every sequence of length 14 with average at most 4 has
$\operatorname{sdeg}(\hat A)\ge 4$, and wrote "We do not know yet".

We prove the following.

**Theorem 1.1.** $L(4)=16$.

**Theorem 1.2.** $L(5)\ge 49$. So $49\le L(5)\le 61$.

Conjecture 5.6 predicts $L(4)=14$ and $L(5)=45$, so it is false for $n=4$
and $n=5$. At $n=4$ the value of $L(n)$ is the upper bound
$R_{n-1}(3)-1$, not the lower bound. Theorem 1.1 answers the question of
[ER21] in the negative: the first 14 entries of the sequence $W$ of
Section 3 have average $15/7$ and Schur degree of the block sums at most 3.

The proof of Theorem 1.1 is short and can be checked by hand. Theorem 1.2
comes from a general lift (Lemma 4.1 and Corollary 4.2) from partitions of
the nonzero elements of $\mathbb{Z}_{m_1}\times\mathbb{Z}_{m_2}$ into sets
that are sumfree in the group.

Conjectures 5.7 and 5.8 remain open. Conjecture 5.7 holds for $2\le n\le 5$ by
the known values [ER21, Table 1] ($44\le 4\cdot 14$, $160\le 5\cdot 45$).
Conjecture 5.8 follows from Conjecture 5.6 at $n=6$, that is, from
$L(6)=161$, and our results do not decide that case (Section 6).

Theorem 1.1, the bound $L(5)\ge49$, Lemma 4.1 and Corollary 4.2 are also
formalized in Lean 4 with Mathlib (Section 7). The upper bound
$L(5)\le61$ uses $R_4(3)\le62$ [FKR04], which is not formalized; the
formal upper bound is $L(5)\le65$.

# 2. Definitions and results of Eliahou and Revuelta

All sumfree sets below, and all sets whose Schur degree we take, are sets
of positive integers, except in the groups of Sections 4 to 6. A set $X$ is *covered by $n$ sumfree sets* when it is a
subset of the union of $n$ sumfree sets. The *Schur degree*
$\operatorname{sdeg}(X)$ is the least $n\ge 1$ such that $n$ sumfree sets
cover $X$ [ER21, Definition 2.1]. For example,
$\operatorname{sdeg}(\{1,\dots,N\})\le n$ holds for $N\le S(n)$ and fails
for $N>S(n)$.

Let $A=(a_1,\dots,a_L)$ be a sequence of positive integers, of length
$|A|=L$. A *block* of $A$ is a run $(a_i,\dots,a_j)$ of consecutive entries
with $1\le i\le j\le L$, and $\hat A$ is the set of the sums of the blocks.
The *average* of $A$ is $\mu(A)=(a_1+\dots+a_L)/L$.

**Definition** [ER21, Definition 5.1]. Let $n\ge2$. Then $L(n)$ is the
smallest positive integer with the following property: every sequence $A$
of positive integers with $|A|=L(n)$ and $\mu(A)\le n$ has
$\operatorname{sdeg}(\hat A)\ge n$.

For $n\ge2$, the inequality $\operatorname{sdeg}(\hat A)\ge n$ holds when no
$n-1$ sumfree sets cover $\hat A$, and it fails when some $n-1$ sumfree sets
cover $\hat A$. The property is about sequences of one length. A sequence of
length $L+1$ and average at most $n$ need not contain $L$ consecutive
entries of average at most $n$, so a lower bound $L(n)\ge m$ needs a
counterexample at every length $L$ with $1\le L<m$.

We use the following results of [ER21], with their numbers in [ER21]; the
preprint [ER20] has the same numbering.

- **[ER21, Proposition 2.5].** If $B$ is a block of $A$, then $\hat B\subseteq\hat A$.
- **[ER21, Proposition 2.7].** Let $X=\{x_0<x_1<\dots<x_L\}$ be a finite set of
  integers, and let $A=\Delta X=(x_1-x_0,\dots,x_L-x_{L-1})$ be its sequence
  of jumps. Then $\hat A=(X-X)\cap\mathbb{Z}_{>0}$.
- **[ER21, Proposition 3.2].** If $B$ is a block of $A$, then
  $\operatorname{sdeg}(\hat B)\le\operatorname{sdeg}(\hat A)$.
- **[ER21, Theorem 4.1].** If $|A|\ge R_q(3)-1$, then
  $\operatorname{sdeg}(\hat A)\ge q+1$.
- **[ER21, Proposition 5.3].** $S(n-1)+1\le L(n)\le R_{n-1}(3)-1$ for $n\ge2$.
- **[ER21, Theorem 5.4].** $S(n)\le n\,L(n)$.

# 3. The value $L(4)=16$

Let
$$W=(1,1,1,6,1,1,1,7,1,1,1,6,1,1,1).$$
Its length is 15 and its sum is 31. Its prefix sums form the set
$$X=\{0,1,2,3\}+\{0,9,19,28\}=\{0,1,2,3,9,10,11,12,19,20,21,22,28,29,30,31\},$$
and $W=\Delta X$.

**Lemma 3.1.** $\hat W=[1,3]\cup[6,13]\cup[16,22]\cup[25,31]$. This set
has 25 elements.

**Proof.** By [ER21, Proposition 2.7], $\hat W$ is the set of positive differences
of elements of $X$. Write each element of $X$ as $u+t$ with
$u\in\{0,1,2,3\}$ and $t\in T=\{0,9,19,28\}$. Two elements with the same
$t$ give the differences 1, 2 and 3. The positive differences of $T$ are 9,
10, 19 and 28. A positive difference $t-t'$ plus $u-u'\in[-3,3]$ gives the
intervals $[6,12]$, $[7,13]$, $[16,22]$ and $[25,31]$, and every value in
these intervals occurs. $\square$

**Lemma 3.2.** The three sets
$$
\begin{aligned}
C_0&=\{1,3,8,12,18,22,28\},\\
C_1&=\{2,6,7,10,11,25,26,29,30\},\\
C_2&=\{9,13,16,17,19,20,21,27,31\}
\end{aligned}
$$
are sumfree, and they partition $\hat W$. So
$\operatorname{sdeg}(\hat W)\le 3$.

**Proof.** The sets are disjoint, they have $7+9+9=25$ elements, and they
lie in $\hat W$; by Lemma 3.1 they partition $\hat W$. The table lists, for
each set, every sum $x+y$ with $x\le y$ in the set (including $x=y$) and
$x+y\le 31$. No listed sum is in the set. Sums above 31 are not in
$\hat W$.

| set | sums $x+y\le 31$ with $x\le y$ |
|---|---|
| $C_0$ | 2, 4, 6, 9, 11, 13, 15, 16, 19, 20, 21, 23, 24, 25, 26, 29, 30, 31 |
| $C_1$ | 4, 8, 9, 12, 13, 14, 16, 17, 18, 20, 21, 22, 27, 28, 31 |
| $C_2$ | 18, 22, 25, 26, 28, 29, 30 |

$\square$

**Proof of Theorem 1.1.** By [ER21, Proposition 5.3] and $R_3(3)=17$ [GG55],
$L(4)\le 16$. (Directly: every sequence of length $16=R_3(3)-1$ has
$\operatorname{sdeg}(\hat A)\ge4$ by [ER21, Theorem 4.1].)

For the lower bound, let $1\le L\le 15$ and let $B$ be the block of the
first $L$ entries of $W$. The sums of these blocks, for $L=1,\dots,15$, are
$$1,2,3,9,10,11,12,19,20,21,22,28,29,30,31.$$
Each is at most $4L$, so $\mu(B)\le 4$. By [ER21, Proposition 3.2] and Lemma 3.2,
$\operatorname{sdeg}(\hat B)\le\operatorname{sdeg}(\hat W)\le 3<4$. So the
defining property of $L(4)$ fails at every length $L\le 15$, and
$L(4)=16$. $\square$

**Remark 3.3 (least sums; computer check).** A SAT computation shows that
every sequence $A$ of length 14 with $\operatorname{sdeg}(\hat A)\le 3$ has
sum at least 30. The solver CaDiCaL [BFF24] reported that the formula which
allows every sum at most 29 is unsatisfiable, and drat-trim [WHH14]
verified the proof of unsatisfiability. An independent exhaustive search
without a SAT solver agrees. The first 14 entries of $W$ have sum 30. By
[ER21, Proposition 3.2] the least sum at length 15 is then 31, which $W$ attains.
An exhaustive search found that $W$ is the only sequence $A$ of length 15
with sum at most 31 and $\operatorname{sdeg}(\hat A)\le 3$.

**Remark 3.4 (a Ramsey colouring; computer check).** The construction in
the proof of [ER21, Theorem 4.1] turns Lemma 3.2 into a 3-colouring of the
edges of the complete graph on $X$: the edge $\{x,y\}$ gets the index of the
set that contains $|x-y|$. This colouring of $K_{16}$ has no monochromatic
triangle. A computer check shows that each colour class is a strongly
regular graph with parameters $(16,5,0,2)$, isomorphic to the Clebsch graph
(the folded 5-cube).

# 4. A lift from finite abelian groups

Let $G$ be an abelian group. A set $C\subseteq G$ is *sumfree in $G$* when
there are no $x,y,z\in C$ with $x+y=z$ in $G$ ($x=y$ allowed).

**Lemma 4.1.** Let $m_1,m_2\ge1$ and $q\ge1$, and let
$G=\mathbb{Z}_{m_1}\times\mathbb{Z}_{m_2}$. Suppose that the sets
$C_1,\dots,C_q$ are sumfree in $G$ and that their union contains
$G\setminus\{0\}$. Let $M\ge 3m_1-2$, let
$$X=\{u+Mj:\ 0\le u\le m_1-1,\ 0\le j\le m_2-1\},$$
and let $A=\Delta X$. Then $|A|=m_1m_2-1$, every entry of $A$ is positive,
$\operatorname{sdeg}(\hat A)\le q$, and for $0\le L\le m_1m_2-1$ the sum of
the first $L$ entries of $A$ is
$$x_L=(L\bmod m_1)+M\lfloor L/m_1\rfloor .$$

**Proof.** Since $M\ge m_1$, the $m_1m_2$ numbers $u+Mj$ are distinct. In
increasing order they are $x_L=u+Mj$ with $L=jm_1+u$ and $0\le u\le m_1-1$.
So $|A|=m_1m_2-1$, the entries of $A$ are positive, and the sum of the
first $L$ entries is $x_L-x_0=x_L$.

By [ER21, Proposition 2.7], $\hat A=(X-X)\cap\mathbb{Z}_{>0}$. Let $d\in\hat A$,
$d=(u+Mj)-(u'+Mj')$, and put $r=u-u'$ and $e=j-j'$. Then $d=r+Me$ with
$|r|\le m_1-1$ and $|e|\le m_2-1$. If $e<0$, then $d\le (m_1-1)-M<0$, which
is false. So $e\ge0$, and if $e=0$ then $r=d\ge1$.

The pair $(r,e)$ depends only on $d$. Indeed, if $r+Me=r'+Me'$ with
$|r|,|r'|\le m_1-1$, then $M|e-e'|=|r'-r|\le 2(m_1-1)<M$, so $e=e'$ and
$r=r'$. Put
$$\pi(d)=(r\bmod m_1,\ e\bmod m_2)\in G.$$
Then $\pi(d)\ne0$: we have $0\le e\le m_2-1$, and $e=0$ gives
$1\le r\le m_1-1$. Give $d$ an index $i$ with $\pi(d)\in C_i$.

Suppose that $d_1+d_2=d_3$ with $d_1,d_2,d_3\in\hat A$ ($d_1=d_2$ allowed).
Then $r_1+r_2-r_3=M(e_3-e_1-e_2)$. The left side has absolute value at most
$3(m_1-1)<M$, so both sides are 0. So $\pi(d_1)+\pi(d_2)=\pi(d_3)$ in $G$,
and $d_1,d_2,d_3$ do not all have the same index, because each $C_i$ is
sumfree in $G$. So the $q$ index classes are sumfree sets that cover
$\hat A$, and $\operatorname{sdeg}(\hat A)\le q$. $\square$

The hypothesis $q\ge1$ is needed only in one degenerate case: for
$m_1=m_2=1$ the sequence $A$ is empty, and $\operatorname{sdeg}(\emptyset)=1$.
The proof uses $M\ge 3m_1-2$. For smaller $M$ the map $\pi$ need not
respect sums. For example, for $m_1=m_2=2$ and $M=3$ we have
$X=\{0,1,3,4\}$, $\hat A=\{1,2,3,4\}$, $\pi(1)=(1,0)$ and $\pi(2)=(1,1)$;
so $1+1=2$, but $\pi(1)+\pi(1)=(0,0)\ne\pi(2)$. The conclusion can still
hold for smaller $M$: for $m_1=m_2=7$ and $M=16$ a SAT solver found a
cover of $\hat A$ by four sumfree sets.

**Corollary 4.2.** Let $n\ge3$ and $m_1,m_2\ge1$. If $n-1$ sets that are
sumfree in $\mathbb{Z}_{m_1}\times\mathbb{Z}_{m_2}$ cover its nonzero
elements, then $L(n)\ge m_1m_2$.

**Proof.** Take $M=3m_1-2$ in Lemma 4.1. For $1\le L\le m_1m_2-1$, write
$L=jm_1+u$ with $0\le u\le m_1-1$. Then
$x_L=u+(3m_1-2)j<3(u+m_1j)=3L$ when $L\ge1$. So the first $L$ entries of
$A$ form a block $B$ with $\mu(B)<3\le n$, and
$\operatorname{sdeg}(\hat B)\le\operatorname{sdeg}(\hat A)\le n-1$ by
[ER21, Proposition 3.2]. So the defining property of $L(n)$ fails at every length
$L\le m_1m_2-1$, and $L(n)\ge m_1m_2$. $\square$

**Remarks.**

1. For $m_2=1$ the corollary gives nothing new. If $\mathbb{Z}_N\setminus\{0\}$
   is covered by $n-1$ sets sumfree in $\mathbb{Z}_N$, then their restriction
   to $[1,N-1]$ is a cover by $n-1$ sumfree sets of integers, so
   $N-1\le S(n-1)$ and the bound $L(n)\ge N$ is at most the lower bound of
   [ER21, Proposition 5.3]. The gain comes from non-cyclic groups.
2. A partition of $(\mathbb{Z}_4\times\mathbb{Z}_4)\setminus\{0\}$ into
   three sets that are sumfree in the group exists [WSW72], as cited in
   [Ana23]. With it, Corollary 4.2 gives
   $L(4)\ge16$ again.
3. A cover of $G\setminus\{0\}$ by $q$ sets that are sumfree in $G$ gives a
   $q$-colouring of the edges of the complete graph on $|G|$ vertices with
   no monochromatic triangle. For symmetric sets the edge $\{g,h\}$ gets
   the colour of $g-h$ [GG55]; for sets that are not symmetric one uses an
   ordering of $G$ [AH72], as cited in [BCR25]. So $|G|<R_q(3)$, and Corollary 4.2 never gives
   more than the upper bound of [ER21, Proposition 5.3].
4. Eliahou and Revuelta also pull sumfree sets back along maps. By
   [ER21, Proposition 3.4], $\operatorname{sdeg}(f^{-1}(Y))\le\operatorname{sdeg}(Y)$
   for a morphism $f$ of abelian groups. By [ER21, Theorem 4.3], a sequence
   $A$ with $|A|\le R_n(3)-2$ that generates a subgroup isomorphic to
   $\mathbb{Z}^{|A|}$ has $\operatorname{sdeg}(\hat A)\le n$. In
   $\mathbb{Z}$ such a sequence has length at most 1; [ER21, Remark 4.4]
   notes that the conclusion also holds for $A=(1,3,3^2,\dots,3^{N-1})$,
   whose averages are large. So these results give no lower bound for
   $L(n)$. The map $\pi$ of Lemma 4.1 is not a morphism from
   $\mathbb{Z}$ to $G$; it respects only the sums $d_1+d_2=d_3$ inside
   $\hat A$. What Lemma 4.1 adds is a sequence of positive integers for which
   such a map exists and, with $M=3m_1-2$, all prefix averages are less
   than 3.

# 5. The bound $L(5)\ge 49$

**Proof of Theorem 1.2.** The four sets in the table partition
$(\mathbb{Z}_7\times\mathbb{Z}_7)\setminus\{0\}$. Each has 12 elements, is
closed under negation, and is sumfree in the group; this is a finite check
of $4\cdot 12^2$ sums.

| set | elements $(a,b)\in\mathbb{Z}_7\times\mathbb{Z}_7$ |
|---|---|
| $C_0$ | (0,2) (0,5) (1,4) (2,3) (2,4) (3,2) (3,3) (4,4) (4,5) (5,3) (5,4) (6,3) |
| $C_1$ | (1,1) (1,3) (1,5) (1,6) (3,0) (3,5) (4,0) (4,2) (6,1) (6,2) (6,4) (6,6) |
| $C_2$ | (0,3) (0,4) (1,0) (1,2) (2,1) (2,6) (3,4) (4,3) (5,1) (5,6) (6,0) (6,5) |
| $C_3$ | (0,1) (0,6) (2,0) (2,2) (2,5) (3,1) (3,6) (4,1) (4,6) (5,0) (5,2) (5,5) |

Corollary 4.2 with $n=5$ and $m_1=m_2=7$ gives $L(5)\ge49$. The upper
bound $L(5)\le R_4(3)-1\le 61$ follows from [ER21, Proposition 5.3] and
$R_4(3)\le 62$ [FKR04, Rad26]. $\square$

With $M=19$ the sequence of Lemma 4.1 is
$$A=(1^6,13,1^6,13,1^6,13,1^6,13,1^6,13,1^6,13,1^6),$$
where $1^6$ stands for six entries equal to 1. It has length 48, sum 120,
and $|\hat A|=84$; the largest average of a prefix is $19/7$. A direct
computer check, with no solver, confirms that the colouring of the proof
of Lemma 4.1 has no monochromatic solution of $x+y=z$ in $\hat A$.

A partition of $(\mathbb{Z}_7\times\mathbb{Z}_7)\setminus\{0\}$ of this kind
gives $R_4(3)\ge 50$ by Remark 3 of Section 4, a bound that Anabanti [Ana17]
credits to Whitehead [Whi73]. The best known lower bound is
$R_4(3)\ge 51$ [Chu73, Rad26]. Our partition was found by a SAT solver.

**The limits of the lift at $n=5$ (computer check).** Corollary 4.2 gives
no bound above $L(5)\ge49$:

- a cyclic group $\mathbb{Z}_N$ with $N\ge46$ has no cover of its nonzero
  elements by 4 sets sumfree in the group, because the restriction to
  $[1,N-1]$ would give $S(4)\ge 45$ (Remark 1 of Section 4);
- the non-cyclic abelian groups of order 50 to 60 have no such cover. There
  are seven such groups (of orders 50, 52, 54, 56 and 60). For each, CaDiCaL
  reported the formula unsatisfiable, and drat-trim verified the proof;
- a group $\mathbb{Z}_{m_1}\times\mathbb{Z}_{m_2}$ of order at least 62 has
  no such cover, because Corollary 4.2 would give $L(5)\ge62>61$; and 61 is
  prime.

Anabanti [Ana17, Ana23] excludes partitions into four symmetric sets for
all groups of order 51 to 61; the computation above does not assume
symmetry. We know no sequence of length 49 with average at most 5 and
$\operatorname{sdeg}(\hat A)\le 4$; such a sequence would give
$L(5)\ge 50$. The exact value of $L(5)$ is open.

# 6. The case $n=6$

For $n=6$, [ER21, Proposition 5.3] and $R_5(3)\le 307$ [Rad26] give
$161\le L(6)\le 306$. Conjecture 5.6 at $n=6$, that is $L(6)=161$, is the
case that would give Conjecture 5.8.

By Corollary 4.2, a cover of the nonzero elements of a group
$\mathbb{Z}_{m_1}\times\mathbb{Z}_{m_2}$ of order at least 162 by five sets
that are sumfree in the group would refute Conjecture 5.6 at $n=6$. By
Remark 3 of Section 4 it would also give $R_5(3)\ge m_1m_2+1\ge 163$, which
is above the best known lower bound $R_5(3)\ge 162$ [Exo94, Rad26]. A cyclic
group of order at least 162 has no such cover, because $S(5)=160$. So a
refutation at $n=6$ through Corollary 4.2 needs a non-cyclic group of order
162 to 306 with such a cover, and it would improve the lower bound for
$R_5(3)$. Our solver searches did not find one; they were not exhaustive.

# 7. Formal verification

The main results of Sections 3 to 5 are formalized in Lean 4 [MU21] with
Mathlib [mC20] (Lean `v4.35.0-rc3`): Theorem 1.1, the bound $L(5)\ge49$ of
Theorem 1.2, Lemma 4.1 and Corollary 4.2. The remarks and the computer
checks are not formalized. The definitions follow [ER21], with sets of natural
numbers and sequences given as lists of natural numbers; for a subset of
the positive integers the Schur degree is the same in $\mathbb{N}$ and in
$\mathbb{Z}$. The formal statements are:

- $L(4)=16$;
- $49\le L(5)\le 65$;
- Lemma 4.1, with the sequence $A$ given by its prefix sums $x_L$, and
  Corollary 4.2;
- [ER21, Theorem 4.1] for sequences of natural numbers, and the upper
  bound $L(k+1)\le\rho(k)-1$ of [ER21, Proposition 5.3], both with
  $\rho(k)$ in place of $R_k(3)$, where $\rho(0)=2$ and
  $\rho(k+1)=(k+1)(\rho(k)-1)+2$.

The bound $\rho(k)$ is the pigeonhole upper bound for $R_k(3)$, proved in
the formalization. Since $\rho(3)=17$, the formal proof of $L(4)\le16$
proves the bound $R_3(3)\le17$ that it needs. Since $\rho(4)=66>62$, the formal
upper bound for $L(5)$ is 65, not 61. The finite checks (the sumfree and
covering parts of Lemma 3.2 and of the table of Section 5, and the prefix
sums of $W$) are done by the Lean kernel with `decide`, without native
code. The only axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

The six main statements are also checked with `lake comparator` [LFRO],
which is part of Lake in the Lean toolchain. It compares the statements,
with every definition that they use, against a separate file that imports
only Mathlib, and it checks the proofs with the Lean kernel and with the
independent kernels nanoda and con-ron.

**Data and code availability.** The Lean source, the comparator
configuration and programs for the computer checks are in the repository
<https://github.com/mysticflounder/schur-degree-block-sums>. The programs
check the witnesses of Theorems 1.1 and 1.2 and the parameters of the
colouring of Remark 3.4 without a solver, make the exhaustive searches of
Remark 3.3, and write the SAT formulas of Remark 3.3 and of Section 5. The
repository also gives the SHA-256 digests of these formulas and their DRAT
proofs. The isomorphism test of Remark 3.4 and the solver searches of
Section 6 were made with programs that are not in the repository.

# 8. Related work

We found no work after [ER21] on $L(n)$ or on Conjectures 5.6 to 5.8.
The citation databases Crossref, OpenAlex, OpenCitations and Semantic
Scholar list no work that cites [ER21] (September 2026). The textbook
[Jun23] lists [ER21] among its references; we have not seen the text that
cites it.

The use of partitions of finite groups into sumfree sets for Ramsey
colourings is classical [GG55, AH72, Ana17, Ana23]. Our searches (the
citation databases above, and web searches for "Schur degree" and for the
bound $n(S(n-1)+1)$, September 2026) found no earlier application of such
partitions to block sums or to the Schur degree.

# Acknowledgements and use of AI tools

The sequence $W$, the lift of Section 4, the proofs, the computer checks
and the Lean formalization were produced with the AI system Claude
(Anthropic; model Claude Opus 5.5) under the direction of the author, on
25 and 26 September 2026. Independent Claude agents audited the proofs and
the computations with their own code. A GPT model (OpenAI), consulted by
the author, pointed out that the formal upper bound for $L(5)$ is weaker
than the bound of Theorem 1.2. The author has checked the content and
takes responsibility for it.

# References

- [AH72] H. L. Abbott, D. Hanson, A problem of Schur and its
  generalizations, Acta Arith. 20(2) (1972), 175–187.
  doi:10.4064/aa-20-2-175-187.
- [Ana17] C. S. Anabanti, A counterexample on a group partitioning problem,
  Birkbeck Mathematics Preprint Series, Preprint No. 37, Birkbeck,
  University of London (2017), 7 pp.
  <https://eprints.bbk.ac.uk/id/eprint/26765>.
- [Ana23] C. S. Anabanti, The Ramsey number $R_4(3)$ is not solvable by
  group partition means, Quasigroups Related Systems 31(2) (2023),
  165–174. doi:10.56415/qrs.v31.12.
- [Bau61] L. D. Baumert, Sum-free sets, J.P.L. Research Summary No. 36-10,
  Vol. 1 (1961), 16–18.
- [BCR25] A. Bishnoi, W. Cames van Batenburg, A. Ravi, The chromatic number
  of finite projective spaces, arXiv:2512.01760v3 (2026).
- [BFF24] A. Biere, T. Faller, K. Fazekas, M. Fleury, N. Froleyks,
  F. Pollitt, CaDiCaL 2.0, in: Computer Aided Verification (CAV 2024),
  Lecture Notes in Comput. Sci. 14681, Springer (2024), 133–152.
  doi:10.1007/978-3-031-65627-9_7.
- [Chu73] F. R. K. Chung, On the Ramsey numbers $N(3,3,\dots,3;2)$,
  Discrete Math. 5 (1973), 317–321.
- [ER20] S. Eliahou, M. P. Revuelta, The Schur degree of additive sets,
  preprint, arXiv:2006.01502v1 (2020).
- [ER21] S. Eliahou, M. P. Revuelta, The Schur degree of additive sets,
  Discrete Math. 344(5) (2021), Article 112332.
  doi:10.1016/j.disc.2021.112332.
- [Exo94] G. Exoo, A lower bound for Schur numbers and multicolor Ramsey
  numbers of $K_3$, Electron. J. Combin. 1 (1994), #R8.
  doi:10.37236/1188.
- [FKR04] S. E. Fettes, R. L. Kramer, S. P. Radziszowski, An upper bound of
  62 on the classical Ramsey number $R(3,3,3,3)$, Ars Combin. 72 (2004),
  41–63.
- [FS00] H. Fredricksen, M. M. Sweet, Symmetric sum-free partitions and
  lower bounds for Schur numbers, Electron. J. Combin. 7 (2000), #R32.
  doi:10.37236/1510.
- [GG55] R. E. Greenwood, A. M. Gleason, Combinatorial relations and
  chromatic graphs, Canad. J. Math. 7 (1955), 1–7.
  doi:10.4153/CJM-1955-001-4.
- [Heu18] M. J. H. Heule, Schur number five, in: Proceedings of the AAAI
  Conference on Artificial Intelligence 32(1) (AAAI-18) (2018), 6598–6606.
  doi:10.1609/aaai.v32i1.12209. Preprint arXiv:1711.08076v1 (2017).
- [Jun23] V. Jungić, Basics of Ramsey Theory, CRC Press, Boca Raton, FL
  (2023). doi:10.1201/9781003286370.
- [LFRO] Lean FRO, `lake comparator`, in Lake, Lean 4 toolchain
  v4.35.0-rc3, software. <https://github.com/leanprover/lean4>.
- [mC20] The mathlib Community, The Lean mathematical library, in:
  Proceedings of the 9th ACM SIGPLAN International Conference on Certified
  Programs and Proofs (CPP 2020), ACM (2020), 367–381.
  doi:10.1145/3372885.3373824.
- [MU21] L. de Moura, S. Ullrich, The Lean 4 theorem prover and programming
  language, in: Automated Deduction – CADE 28, Lecture Notes in Comput.
  Sci. 12699, Springer (2021), 625–635. doi:10.1007/978-3-030-79876-5_37.
- [Rad26] S. P. Radziszowski, Small Ramsey numbers, Electron. J. Combin.,
  Dynamic Survey DS1, revision 18 (2026). doi:10.37236/21.
- [Whi73] E. G. Whitehead Jr., The Ramsey number $N(3,3,3,3;2)$, Discrete
  Math. 4(4) (1973), 389–396. doi:10.1016/0012-365X(73)90174-X.
- [WHH14] N. Wetzler, M. J. H. Heule, W. A. Hunt Jr., DRAT-trim: Efficient
  checking and trimming using expressive clausal proofs, in: Theory and
  Applications of Satisfiability Testing – SAT 2014, Lecture Notes in
  Comput. Sci. 8561, Springer (2014), 422–429.
  doi:10.1007/978-3-319-09284-3_31.
- [WSW72] W. D. Wallis, J. Seberry Wallis, A. P. Street, Combinatorics: Room
  Squares, Sum-Free Sets, Hadamard Matrices, Lecture Notes in Math. 292,
  Springer (1972). doi:10.1007/BFb0069907.
