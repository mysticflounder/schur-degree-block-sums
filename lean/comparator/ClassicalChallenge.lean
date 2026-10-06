/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib

/-!
# Comparator challenge: the Eliahou–Revuelta number `L(n)`

This file imports Mathlib only. It states the six headline theorems of the
`ClassicalSchur` library as `sorry` stubs, so that a reviewer can read the
claims here without the rest of the repository.

Source of the definitions: S. Eliahou and M. P. Revuelta, *The Schur degree of
additive sets*, Discrete Math. 344(5) (2021) 112332,
doi:10.1016/j.disc.2021.112332 (arXiv:2006.01502), cited below as ER.
ER Conjecture 5.6 states `L(4) = 14` and `L(5) = 45`; the first two theorems
below show that it is false at `n = 4` and at `n = 5`.

The definitions below are copies of the definitions of the `ClassicalSchur`
library, in the namespace `ClassicalSchurClaims`. `ClassicalSolution` repeats
them word for word. The comparator checks that every constant that a statement
uses is the same, with the same value, in the two modules; so these
definitions are the ones that the proofs use.

Deliberate differences from ER:

* The ambient set is `ℕ`, not `ℤ`. For `X ⊆ ℕ` the least number of sumfree
  sets that cover `X` is the same in `ℕ` and in `ℤ`.
* `erL n` is defined for every `n`; ER define `L(n)` for `n ≥ 2`.
* `average [] = 0`; ER do not define the average of an empty sequence. `erL`
  uses only lengths `L > 0`.
* `ramseyBound k` is the pigeonhole bound for the triangle Ramsey number
  `R_k(3)`, not `R_k(3)`: `ramseyBound 3 = 17 = R_3(3)`, and
  `ramseyBound 4 = 66`.
-/

@[expose] public section

namespace ClassicalSchurClaims

/-- A set of naturals is sumfree when it has no `x, y, z` with `x + y = z`;
`x = y` is allowed (ER §2.3: `(S + S) ∩ S = ∅`). -/
def SumFree (S : Set ℕ) : Prop := ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

/-- `X` is covered by `n` sumfree sets (ER Definition 2.1). -/
def CoveredBySumFree (X : Set ℕ) (n : ℕ) : Prop :=
  ∃ C : Fin n → Set ℕ, (∀ i, SumFree (C i)) ∧ X ⊆ ⋃ i, C i

/-- The Schur degree (ER Definition 2.1): the least `n ≥ 1` such that `X` is
covered by `n` sumfree sets, and `⊤` when there is no such `n`. -/
noncomputable def sdeg (X : Set ℕ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' {n | 1 ≤ n ∧ CoveredBySumFree X n})

/-- The block sums `Â` of a sequence `A` (ER Notation 2.2): the sums of the
nonempty runs of consecutive entries of `A`. -/
def blockSums (A : List ℕ) : Set ℕ :=
  {s | ∃ B : List ℕ, B <:+: A ∧ B ≠ [] ∧ B.sum = s}

/-- The average `μ(A)` of a sequence. -/
def average (A : List ℕ) : ℚ := (A.sum : ℚ) / A.length

/-- The property of ER Definition 5.1 at length `L`: every sequence of
positive integers of length `L` and average at most `n` has
`sdeg(Â) ≥ n`. -/
def ERProperty (n L : ℕ) : Prop :=
  ∀ A : List ℕ, A.length = L → (∀ a ∈ A, 0 < a) → average A ≤ n →
    (n : ℕ∞) ≤ sdeg (blockSums A)

/-- `L(n)` of ER Definition 5.1: the least positive integer `L` with
`ERProperty n L`. -/
noncomputable def erL (n : ℕ) : ℕ := sInf {L | 0 < L ∧ ERProperty n L}

/-- The pigeonhole upper bound for the triangle Ramsey numbers:
`2, 3, 6, 17, 66, …`. -/
def ramseyBound : ℕ → ℕ
  | 0 => 2
  | k + 1 => (k + 1) * (ramseyBound k - 1) + 2

/-- A subset of an additive group is sumfree in the group when it has no
`x, y, z` with `x + y = z` (`x = y` allowed). -/
def GroupSumFree {G : Type*} [Add G] (S : Set G) : Prop := ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

/-- The `L`-th element, in increasing order, of `X = {u + M·j}`: with
`L = j·m₁ + u` and `u < m₁` it is `u + M·j`. -/
def liftPrefix (m₁ M L : ℕ) : ℕ := L % m₁ + M * (L / m₁)

/-- The sequence `A = ΔX` of jumps of `X = {u + M·j : u < m₁, j < m₂}`. -/
def liftSeq (m₁ m₂ M : ℕ) : List ℕ :=
  (List.range (m₁ * m₂ - 1)).map fun k => liftPrefix m₁ M (k + 1) - liftPrefix m₁ M k

/-- `L(4) = 16`. ER Conjecture 5.6 states `L(4) = 14`. -/
theorem erL_four : erL 4 = 16 := sorry

/-- `49 ≤ L(5) ≤ 65`. ER Conjecture 5.6 states `L(5) = 45`. -/
theorem erL_five_bounds : 49 ≤ erL 5 ∧ erL 5 ≤ 65 := sorry

/-- If the nonzero elements of `ℤ_{m₁} × ℤ_{m₂}` are covered by `n − 1` sets
that are sumfree in the group, then `L(n) ≥ m₁m₂`. The sets need not be
disjoint. -/
theorem le_erL_of_groupPartition {n m₁ m₂ : ℕ} (hn : 3 ≤ n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (C : Fin (n - 1) → Set (ZMod m₁ × ZMod m₂)) (hC : ∀ i, GroupSumFree (C i))
    (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) : m₁ * m₂ ≤ erL n := sorry

/-- The lift: for `M ≥ 3m₁ − 2`, the jump sequence `liftSeq m₁ m₂ M` has
length `m₁m₂ − 1` and positive entries, a cover of the nonzero elements of
`ℤ_{m₁} × ℤ_{m₂}` by `q ≥ 1` sets that are sumfree in the group bounds the
Schur degree of its block sums by `q`, and its prefix sums are
`L % m₁ + M·(L / m₁)`. -/
theorem lift_lemma {m₁ m₂ q M : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hq : 0 < q)
    (hM : 3 * m₁ - 2 ≤ M) (C : Fin q → Set (ZMod m₁ × ZMod m₂))
    (hC : ∀ i, GroupSumFree (C i)) (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) :
    (liftSeq m₁ m₂ M).length = m₁ * m₂ - 1 ∧ (∀ a ∈ liftSeq m₁ m₂ M, 0 < a) ∧
      sdeg (blockSums (liftSeq m₁ m₂ M)) ≤ q ∧
      ∀ L ≤ m₁ * m₂ - 1, ((liftSeq m₁ m₂ M).take L).sum = L % m₁ + M * (L / m₁) := sorry

/-- ER Theorem 4.1 for sequences of naturals, with `ramseyBound k` in place
of `R_k(3)`: a sequence of length at least `ramseyBound k − 1` has
`sdeg(Â) ≥ k + 1`. -/
theorem le_sdeg_blockSums {k : ℕ} {A : List ℕ} (hA : ramseyBound k ≤ A.length + 1) :
    ((k + 1 : ℕ) : ℕ∞) ≤ sdeg (blockSums A) := sorry

/-- ER Proposition 5.3 (upper bound), with `ramseyBound k` in place of
`R_k(3)`: `L(k + 1) ≤ ramseyBound k − 1`. -/
theorem erL_le (k : ℕ) : erL (k + 1) ≤ ramseyBound k - 1 := sorry

end ClassicalSchurClaims
