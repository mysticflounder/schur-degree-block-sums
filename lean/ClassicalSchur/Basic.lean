/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib

/-!
# Schur degree of block-sum sets (Eliahou–Revuelta)

Definitions from S. Eliahou and M. P. Revuelta, *The Schur degree of additive
sets*, Discrete Math. 344(5) (2021) 112332, doi:10.1016/j.disc.2021.112332
(arXiv:2006.01502), cited below as ER.

* `SumFree S`: no `x, y, z ∈ S` with `x + y = z` (`x = y` allowed; ER §2.3).
* `CoveredBySumFree X n`: `n` sumfree sets cover `X` (ER Definition 2.1).
* `sdeg X`: the Schur degree, the least `n ≥ 1` with such a cover, `⊤` if none.
* `blockSums A`: the set `Â` of sums of nonempty runs of consecutive entries
  of `A` (ER §2.1, Notation 2.2).
* `ERProperty n L` and `erL n`: the property and the number `L(n)` of ER
  Definition 5.1.

The ambient set is `ℕ`, not `ℤ`: for `X ⊆ ℕ` the least number of sumfree sets
that cover `X` is the same in both.
-/

@[expose] public section

namespace ClassicalSchur

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

/-- A cover by `q ≥ 1` sumfree sets bounds the Schur degree by `q`. -/
theorem sdeg_le_of_coveredBySumFree {X : Set ℕ} {q : ℕ} (hq : 1 ≤ q)
    (h : CoveredBySumFree X q) : sdeg X ≤ q :=
  sInf_le ⟨q, ⟨hq, h⟩, rfl⟩

/-- If no cover by fewer than `n` sumfree sets exists, then `sdeg X ≥ n`. -/
theorem le_sdeg_of_forall_not_covered {X : Set ℕ} {n : ℕ}
    (h : ∀ q, 1 ≤ q → q < n → ¬ CoveredBySumFree X q) : (n : ℕ∞) ≤ sdeg X := by
  refine le_sInf ?_
  rintro _ ⟨q, ⟨hq1, hq⟩, rfl⟩
  by_contra! hlt
  exact h q hq1 (by exact_mod_cast hlt) hq

/-- A cover of `Y` restricts to a cover of any subset of `Y`. -/
theorem CoveredBySumFree.mono {X Y : Set ℕ} {q : ℕ} (hXY : X ⊆ Y)
    (h : CoveredBySumFree Y q) : CoveredBySumFree X q := by
  obtain ⟨C, hC, hY⟩ := h
  exact ⟨C, hC, hXY.trans hY⟩

/-- ER Proposition 2.5: the block sums of a block of `A` are block sums
of `A`. -/
theorem blockSums_mono_of_infix {A B : List ℕ} (h : B <:+: A) :
    blockSums B ⊆ blockSums A := by
  rintro s ⟨B', hB', hne, rfl⟩
  exact ⟨B', hB'.trans h, hne, rfl⟩

/-- Prefix sums are monotone in the index. -/
theorem prefixSum_mono (A : List ℕ) {i j : ℕ} (hij : i ≤ j) :
    (A.take i).sum ≤ (A.take j).sum := by
  have h1 : (A.take j).take i = A.take i := by simp [List.take_take, Nat.min_eq_left hij]
  have h2 := List.sum_take_add_sum_drop (A.take j) i
  rw [h1] at h2
  omega

/-- A difference of two prefix sums is a block sum (ER Proposition 2.7,
one direction). -/
theorem sub_mem_blockSums (A : List ℕ) {i j : ℕ} (hij : i < j) (hj : j ≤ A.length) :
    (A.take j).sum - (A.take i).sum ∈ blockSums A := by
  refine ⟨(A.take j).drop i, ?_, ?_, ?_⟩
  · exact (List.drop_suffix i (A.take j)).isInfix.trans (List.take_prefix j A).isInfix
  · intro h
    have h' := congrArg List.length h
    simp at h'
    omega
  · have h1 : (A.take j).take i = A.take i := by simp [List.take_take, Nat.min_eq_left hij.le]
    have h2 := List.sum_take_add_sum_drop (A.take j) i
    rw [h1] at h2
    omega

/-- Every block sum is a difference of two prefix sums (ER Proposition 2.7,
the other direction). -/
theorem exists_of_mem_blockSums {A : List ℕ} {s : ℕ} (hs : s ∈ blockSums A) :
    ∃ i j, i < j ∧ j ≤ A.length ∧ s = (A.take j).sum - (A.take i).sum := by
  obtain ⟨B, ⟨u, v, rfl⟩, hne, rfl⟩ := hs
  have hB : 0 < B.length := List.length_pos_iff.mpr hne
  refine ⟨u.length, u.length + B.length, by omega, by simp only [List.length_append]; omega, ?_⟩
  have h1 : (u ++ B ++ v).take (u.length + B.length) = u ++ B := by
    rw [show u.length + B.length = (u ++ B).length by simp, List.take_left]
  have h2 : (u ++ B ++ v).take u.length = u := by
    rw [List.append_assoc, List.take_left]
  rw [h1, h2, List.sum_append]
  omega

/-- For a nonempty sequence, `μ(A) ≤ n` holds exactly when the sum is at
most `n` times the length. -/
theorem average_le_iff {A : List ℕ} (hA : 0 < A.length) (n : ℕ) :
    average A ≤ n ↔ A.sum ≤ n * A.length := by
  have hL : (0 : ℚ) < A.length := by exact_mod_cast hA
  rw [average, div_le_iff₀ hL]
  norm_cast

end ClassicalSchur
