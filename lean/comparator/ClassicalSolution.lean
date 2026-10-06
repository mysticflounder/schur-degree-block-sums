/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import ClassicalSchur

/-!
# Comparator solution: the Eliahou–Revuelta number `L(n)`

This file imports the `ClassicalSchur` library and proves the six statements
of `ClassicalChallenge`, with the same names in the namespace
`ClassicalSchurClaims`.

The definitions below are the definitions of `ClassicalChallenge`, word for
word (the comparator checks that they are the same constants). Each is also a
copy of the `ClassicalSchur` definition of the same name, so each proof below
is the library theorem of the same name: the kernel unfolds the definitions
of the two namespaces to the same terms.

Library theorems (all in the `ClassicalSchur` library): `erL_four` and
`erL_five_bounds` (`Values.lean`), `le_erL_of_groupPartition` and
`lift_lemma` (`Lift.lean`), `le_sdeg_blockSums` and `erL_le`
(`Ramsey.lean`).
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

theorem erL_four : erL 4 = 16 := ClassicalSchur.erL_four

theorem erL_five_bounds : 49 ≤ erL 5 ∧ erL 5 ≤ 65 := ClassicalSchur.erL_five_bounds

theorem le_erL_of_groupPartition {n m₁ m₂ : ℕ} (hn : 3 ≤ n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (C : Fin (n - 1) → Set (ZMod m₁ × ZMod m₂)) (hC : ∀ i, GroupSumFree (C i))
    (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) : m₁ * m₂ ≤ erL n :=
  ClassicalSchur.le_erL_of_groupPartition hn hm₁ hm₂ C hC hcov

theorem lift_lemma {m₁ m₂ q M : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hq : 0 < q)
    (hM : 3 * m₁ - 2 ≤ M) (C : Fin q → Set (ZMod m₁ × ZMod m₂))
    (hC : ∀ i, GroupSumFree (C i)) (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) :
    (liftSeq m₁ m₂ M).length = m₁ * m₂ - 1 ∧ (∀ a ∈ liftSeq m₁ m₂ M, 0 < a) ∧
      sdeg (blockSums (liftSeq m₁ m₂ M)) ≤ q ∧
      ∀ L ≤ m₁ * m₂ - 1, ((liftSeq m₁ m₂ M).take L).sum = L % m₁ + M * (L / m₁) :=
  ClassicalSchur.lift_lemma hm₁ hm₂ hq hM C hC hcov

/-- The two copies of `ramseyBound` agree. The elaborator does not unfold a
structural recursion at a variable, so this needs an induction. -/
private theorem ramseyBound_eq (k : ℕ) : ramseyBound k = ClassicalSchur.ramseyBound k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [ramseyBound, ClassicalSchur.ramseyBound, ih]

theorem le_sdeg_blockSums {k : ℕ} {A : List ℕ} (hA : ramseyBound k ≤ A.length + 1) :
    ((k + 1 : ℕ) : ℕ∞) ≤ sdeg (blockSums A) := by
  rw [ramseyBound_eq] at hA
  exact ClassicalSchur.le_sdeg_blockSums hA

theorem erL_le (k : ℕ) : erL (k + 1) ≤ ramseyBound k - 1 := by
  rw [ramseyBound_eq]
  exact ClassicalSchur.erL_le k

end ClassicalSchurClaims
