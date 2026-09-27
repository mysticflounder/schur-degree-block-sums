/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ClassicalSchur.Lift

/-!
# `L(4) = 16` and `49 ≤ L(5) ≤ 65`

Theorems 1.1 and 1.2 of the paper (see `ClassicalSchur.lean`). They refute
Conjecture 5.6 of Eliahou–Revuelta (Discrete Math. 344 (2021) 112332), which
states `L(4) = 14` and `L(5) = 45`.

* `L(4) ≥ 16`: the prefixes of `W = (1,1,1,6,1,1,1,7,1,1,1,6,1,1,1)` have
  average at most 4, and three sumfree sets cover `Ŵ` (Lemma 3.2 of the paper).
* `L(4) ≤ 16`: ER Theorem 4.1 with `ramseyBound 3 = 17`.
* `L(5) ≥ 49`: Corollary 4.2 with a partition of the nonzero elements of
  `ℤ₇ × ℤ₇` into four sets that are sumfree in the group.
* `L(5) ≤ 65`: ER Theorem 4.1 with `ramseyBound 4 = 66`.

The finite checks use kernel `decide`.
-/

namespace ClassicalSchur

/-- The sequence `W` of the paper: length 15, sum 31. -/
def seqW : List ℕ := [1, 1, 1, 6, 1, 1, 1, 7, 1, 1, 1, 6, 1, 1, 1]

/-- The classes `C₀, C₁, C₂` of Lemma 3.2 of the paper. -/
def classesW : Fin 3 → Finset ℕ :=
  ![{1, 3, 8, 12, 18, 22, 28}, {2, 6, 7, 10, 11, 25, 26, 29, 30},
    {9, 13, 16, 17, 19, 20, 21, 27, 31}]

theorem classesW_sumFree : ∀ i, ∀ x ∈ classesW i, ∀ y ∈ classesW i, x + y ∉ classesW i := by
  decide

theorem seqW_prefix_diff_mem :
    ∀ j ≤ 15, ∀ i < j, ∃ t, (seqW.take j).sum - (seqW.take i).sum ∈ classesW t := by
  decide

/-- Lemma 3.2 of the paper: three sumfree sets cover `Ŵ`. -/
theorem coveredBySumFree_blockSums_seqW : CoveredBySumFree (blockSums seqW) 3 := by
  refine ⟨fun i => ↑(classesW i), fun i x hx y hy => classesW_sumFree i x hx y hy, ?_⟩
  intro s hs
  obtain ⟨i, j, hij, hj, rfl⟩ := exists_of_mem_blockSums hs
  obtain ⟨t, ht⟩ := seqW_prefix_diff_mem j (by simpa [seqW] using hj) i hij
  exact Set.mem_iUnion.2 ⟨t, ht⟩

/-- Each prefix of `W` of length `L` has sum at most `4L`. -/
theorem seqW_prefix_sum_le : ∀ L ≤ 15, (seqW.take L).sum ≤ 4 * L := by
  decide

/-- The property of ER Definition 5.1 at `n = 4` fails at every length
`1 ≤ L ≤ 15`: the first `L` entries of `W` are a counterexample. -/
theorem not_erProperty_four {L : ℕ} (h0 : 0 < L) (hL : L ≤ 15) : ¬ ERProperty 4 L := by
  intro hP
  set B := seqW.take L with hB
  have hBlen : B.length = L := by simp [hB, seqW]; omega
  have hBpos : ∀ b ∈ B, 0 < b := fun b hb => by
    have hb' := List.mem_of_mem_take hb
    simp [seqW] at hb'
    omega
  have havg : average B ≤ (4 : ℕ) := by
    rw [average_le_iff (by omega), hBlen]
    exact seqW_prefix_sum_le L hL
  have hcov : CoveredBySumFree (blockSums B) 3 :=
    coveredBySumFree_blockSums_seqW.mono
      (blockSums_mono_of_infix (List.take_prefix L seqW).isInfix)
  have h := (hP B hBlen hBpos havg).trans (sdeg_le_of_coveredBySumFree (by norm_num) hcov)
  norm_cast at h

/-- The property of ER Definition 5.1 holds at `n = 4`, `L = 16`. -/
theorem erProperty_four_sixteen : ERProperty 4 16 :=
  erProperty_of_ramseyBound 3 16 (by rw [ramseyBound_three])

/-- `L(4) = 16`. Conjecture 5.6 of Eliahou–Revuelta states `L(4) = 14`. -/
theorem erL_four : erL 4 = 16 := by
  refine IsLeast.csInf_eq ⟨⟨by norm_num, erProperty_four_sixteen⟩, ?_⟩
  rintro L ⟨h0, hP⟩
  by_contra h
  exact not_erProperty_four h0 (by omega) hP

/-- The four sets of Section 5 of the paper: a partition of the nonzero
elements of `ℤ₇ × ℤ₇` into sets that are sumfree in the group. -/
def partitionZ7Z7 : Fin 4 → Finset (ZMod 7 × ZMod 7) :=
  ![{(0, 2), (0, 5), (1, 4), (2, 3), (2, 4), (3, 2), (3, 3), (4, 4), (4, 5), (5, 3), (5, 4),
      (6, 3)},
    {(1, 1), (1, 3), (1, 5), (1, 6), (3, 0), (3, 5), (4, 0), (4, 2), (6, 1), (6, 2), (6, 4),
      (6, 6)},
    {(0, 3), (0, 4), (1, 0), (1, 2), (2, 1), (2, 6), (3, 4), (4, 3), (5, 1), (5, 6), (6, 0),
      (6, 5)},
    {(0, 1), (0, 6), (2, 0), (2, 2), (2, 5), (3, 1), (3, 6), (4, 1), (4, 6), (5, 0), (5, 2),
      (5, 5)}]

theorem partitionZ7Z7_sumFree :
    ∀ i, ∀ x ∈ partitionZ7Z7 i, ∀ y ∈ partitionZ7Z7 i, x + y ∉ partitionZ7Z7 i := by
  decide

theorem partitionZ7Z7_cover : ∀ g : ZMod 7 × ZMod 7, g ≠ 0 → ∃ i, g ∈ partitionZ7Z7 i := by
  decide

/-- `49 ≤ L(5) ≤ 65`. Conjecture 5.6 of Eliahou–Revuelta states
`L(5) = 45`. -/
theorem erL_five_bounds : 49 ≤ erL 5 ∧ erL 5 ≤ 65 := by
  refine ⟨?_, ?_⟩
  · simpa using le_erL_of_groupPartition (n := 5) (m₁ := 7) (m₂ := 7) (by norm_num)
      (by norm_num) (by norm_num) (fun i => ↑(partitionZ7Z7 i))
      (fun i x hx y hy => partitionZ7Z7_sumFree i x hx y hy)
      (fun g hg => partitionZ7Z7_cover g hg)
  · simpa [ramseyBound_four] using erL_le 4

end ClassicalSchur
