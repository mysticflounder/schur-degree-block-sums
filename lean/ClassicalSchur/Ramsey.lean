/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ClassicalSchur.Basic

/-!
# Monochromatic triangles and ER Theorem 4.1

`TriangleRamsey k N` says: every colouring, with at most `k` colours, of the
pairs `x < y` of a set of at least `N` naturals has a monochromatic triangle.
`ramseyBound` is the pigeonhole recursion `R_{k+1}(3) ≤ (k+1)(R_k(3) − 1) + 2`
from `R_0(3) = 2`, so `ramseyBound 3 = 17` and `ramseyBound 4 = 66`.

With it we prove ER Theorem 4.1 (Eliahou–Revuelta, Discrete Math. 344 (2021)
112332) with `ramseyBound k` in place of the Ramsey number `R_k(3)`: a
sequence of length at least `ramseyBound k − 1` has `sdeg(Â) ≥ k + 1`.
The pairs of prefix indices are coloured by a cover set that holds their
block sum; a monochromatic triangle gives `x + y = z` in one sumfree set.
-/

namespace ClassicalSchur

/-- Every colouring with at most `k` colours of the pairs `x < y` of a set
of at least `N` naturals has a monochromatic triangle. -/
def TriangleRamsey (k N : ℕ) : Prop :=
  ∀ (V K : Finset ℕ) (c : ℕ → ℕ → ℕ), K.card ≤ k → N ≤ V.card →
    (∀ x ∈ V, ∀ y ∈ V, x < y → c x y ∈ K) →
    ∃ x ∈ V, ∃ y ∈ V, ∃ z ∈ V, x < y ∧ y < z ∧ c x y = c y z ∧ c x y = c x z

/-- The pigeonhole upper bound for the triangle Ramsey numbers:
`2, 3, 6, 17, 66, …`. -/
def ramseyBound : ℕ → ℕ
  | 0 => 2
  | k + 1 => (k + 1) * (ramseyBound k - 1) + 2

theorem two_le_ramseyBound (k : ℕ) : 2 ≤ ramseyBound k := by
  cases k <;> simp [ramseyBound]

theorem ramseyBound_three : ramseyBound 3 = 17 := by decide

theorem ramseyBound_four : ramseyBound 4 = 66 := by decide

/-- The pigeonhole bound: `k` colours force a monochromatic triangle on
`ramseyBound k` vertices. -/
theorem triangleRamsey_ramseyBound (k : ℕ) : TriangleRamsey k (ramseyBound k) := by
  induction k with
  | zero =>
    intro V K c hK hV hc
    have hK0 : K = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < V.card by simp [ramseyBound] at hV; omega)
    rcases lt_or_gt_of_ne hab with h | h
    · simpa [hK0] using hc a ha b hb h
    · simpa [hK0] using hc b hb a ha h
  | succ k ih =>
    intro V K c hK hV hc
    have h2 := two_le_ramseyBound (k + 1)
    have hVne : V.Nonempty := by rw [← Finset.card_pos]; omega
    set v := V.min' hVne with hv
    have hvV : v ∈ V := V.min'_mem hVne
    set W := V.erase v with hW
    have hWcard : (k + 1) * (ramseyBound k - 1) + 1 ≤ W.card := by
      rw [hW, Finset.card_erase_of_mem hvV]
      simp only [ramseyBound] at hV
      omega
    have hvW : ∀ w ∈ W, v < w := fun w hw =>
      lt_of_le_of_ne (V.min'_le w (Finset.mem_of_mem_erase hw)) (Finset.ne_of_mem_erase hw).symm
    have hmaps : ∀ w ∈ W, c v w ∈ K := fun w hw =>
      hc v hvV w (Finset.mem_of_mem_erase hw) (hvW w hw)
    have hlt : K.card * (ramseyBound k - 1) < W.card :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hK) (by omega)
    obtain ⟨i, hiK, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
    set U := W.filter fun w => c v w = i with hU
    have hUV : U ⊆ V := fun u hu => Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1
    by_cases hmono : ∃ x ∈ U, ∃ y ∈ U, x < y ∧ c x y = i
    · obtain ⟨x, hx, y, hy, hxy, hcxy⟩ := hmono
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      exact ⟨v, hvV, x, hUV hx, y, hUV hy, hvW x hx'.1, hxy, by rw [hx'.2, hcxy],
        by rw [hx'.2, hy'.2]⟩
    · push Not at hmono
      obtain ⟨x, hx, y, hy, z, hz, h1, h2, h3, h4⟩ := ih U (K.erase i) c
        (by rw [Finset.card_erase_of_mem hiK]; omega) (by omega)
        (fun x hx y hy hxy =>
          Finset.mem_erase.mpr ⟨hmono x hx y hy hxy, hc x (hUV hx) y (hUV hy) hxy⟩)
      exact ⟨x, hUV hx, y, hUV hy, z, hUV hz, h1, h2, h3, h4⟩

/-- If `TriangleRamsey k N` and the sequence has at least `N − 1` entries,
its block sums are not covered by `q ≤ k` sumfree sets. -/
theorem not_coveredBySumFree_blockSums {k N : ℕ} (hR : TriangleRamsey k N)
    {A : List ℕ} (hA : N ≤ A.length + 1) {q : ℕ} (hq : q ≤ k) :
    ¬ CoveredBySumFree (blockSums A) q := by
  classical
  rintro ⟨C, hC, hcov⟩
  have hmem : ∀ p : {p : ℕ × ℕ // p.1 < p.2 ∧ p.2 ≤ A.length},
      ∃ t : Fin q, (A.take p.1.2).sum - (A.take p.1.1).sum ∈ C t := fun p =>
    Set.mem_iUnion.mp (hcov (sub_mem_blockSums A p.2.1 p.2.2))
  choose f hf using hmem
  let col : ℕ → ℕ → ℕ := fun x y =>
    if h : x < y ∧ y ≤ A.length then (f ⟨(x, y), h⟩).val else 0
  have hcol : ∀ x y (h : x < y ∧ y ≤ A.length), col x y = (f ⟨(x, y), h⟩).val :=
    fun x y h => dif_pos h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, h1, h2⟩ :=
    hR (Finset.range (A.length + 1)) (Finset.range q) col (by simpa using hq)
      (by simpa using hA)
      (fun x _ y hy hxy => by
        rw [Finset.mem_range] at hy
        rw [hcol x y ⟨hxy, by omega⟩, Finset.mem_range]
        exact (f _).isLt)
  rw [Finset.mem_range] at hx hy hz
  have hxy' : x < y ∧ y ≤ A.length := ⟨hxy, by omega⟩
  have hyz' : y < z ∧ z ≤ A.length := ⟨hyz, by omega⟩
  have hxz' : x < z ∧ z ≤ A.length := ⟨hxy.trans hyz, by omega⟩
  rw [hcol x y hxy', hcol y z hyz'] at h1
  rw [hcol x y hxy', hcol x z hxz'] at h2
  have m1 := hf ⟨(x, y), hxy'⟩
  have m2 := hf ⟨(y, z), hyz'⟩
  have m3 := hf ⟨(x, z), hxz'⟩
  rw [show f ⟨(y, z), hyz'⟩ = f ⟨(x, y), hxy'⟩ from Fin.ext h1.symm] at m2
  rw [show f ⟨(x, z), hxz'⟩ = f ⟨(x, y), hxy'⟩ from Fin.ext h2.symm] at m3
  have p1 := prefixSum_mono A hxy.le
  have p2 := prefixSum_mono A hyz.le
  refine hC _ _ m1 _ m2 ?_
  convert m3 using 1
  dsimp only
  omega

/-- ER Theorem 4.1, with `ramseyBound k` in place of `R_k(3)`. -/
theorem le_sdeg_blockSums {k : ℕ} {A : List ℕ} (hA : ramseyBound k ≤ A.length + 1) :
    ((k + 1 : ℕ) : ℕ∞) ≤ sdeg (blockSums A) :=
  le_sdeg_of_forall_not_covered fun _ _ hq =>
    not_coveredBySumFree_blockSums (triangleRamsey_ramseyBound k) hA (by omega)

/-- The property of ER Definition 5.1 holds at every length `L` with
`ramseyBound k ≤ L + 1`, whatever the average. -/
theorem erProperty_of_ramseyBound (k L : ℕ) (hL : ramseyBound k ≤ L + 1) :
    ERProperty (k + 1) L := by
  intro A hlen _ _
  exact le_sdeg_blockSums (by omega)

/-- A lower bound for `L(n)` from a lower bound for every length with the
property. The set is nonempty by `erProperty_of_ramseyBound`. -/
theorem le_erL {n m : ℕ} (hn : 1 ≤ n) (h : ∀ L, 0 < L → ERProperty n L → m ≤ L) :
    m ≤ erL n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h2 := two_le_ramseyBound k
  have hne : {L | 0 < L ∧ ERProperty (k + 1) L}.Nonempty :=
    ⟨ramseyBound k - 1, by omega, erProperty_of_ramseyBound k _ (by omega)⟩
  exact le_csInf hne fun L hL => h L hL.1 hL.2

/-- ER Proposition 5.3 (upper bound), with `ramseyBound k` in place of
`R_k(3)`: `L(k + 1) ≤ ramseyBound k − 1`. -/
theorem erL_le (k : ℕ) : erL (k + 1) ≤ ramseyBound k - 1 := by
  have h2 := two_le_ramseyBound k
  exact Nat.sInf_le ⟨by omega, erProperty_of_ramseyBound k _ (by omega)⟩

end ClassicalSchur
