/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ClassicalSchur.Ramsey

/-!
# A lift from `ℤ_{m₁} × ℤ_{m₂}` to block-sum sets

Lemma 4.1 and Corollary 4.2 of the paper (see `ClassicalSchur.lean`).
Let `X = {u + M·j : 0 ≤ u < m₁, 0 ≤ j < m₂}` with `M ≥ 3m₁ − 2`, and let
`A = ΔX` be its sequence of jumps (`liftSeq`). The `L`-th element of `X` in
increasing order is `liftPrefix m₁ M L = L % m₁ + M·(L / m₁)`. A block sum
`d` of `A` has a unique form `d = r + M·e` with `|r| ≤ m₁ − 1`; the map
`d ↦ (r mod m₁, e mod m₂)` sends `Â` into the nonzero elements of the group
and sends `d₁ + d₂ = d₃` to a sum in the group. So a partition of the
nonzero elements into `q` sets that are sumfree in the group gives a cover
of `Â` by `q` sumfree sets (Lemma 4.1). With `M = 3m₁ − 2` all prefix averages
are at most 3, which gives `L(n) ≥ m₁m₂` (Corollary 4.2).
-/

namespace ClassicalSchur

/-- A subset of an additive group is sumfree in the group when it has no
`x, y, z` with `x + y = z` (`x = y` allowed). -/
def GroupSumFree {G : Type*} [Add G] (S : Set G) : Prop := ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

/-- The `L`-th element, in increasing order, of `X = {u + M·j}`: with
`L = j·m₁ + u` and `u < m₁` it is `u + M·j`. -/
def liftPrefix (m₁ M L : ℕ) : ℕ := L % m₁ + M * (L / m₁)

/-- The sequence `A = ΔX` of jumps of `X = {u + M·j : u < m₁, j < m₂}`. -/
def liftSeq (m₁ m₂ M : ℕ) : List ℕ :=
  (List.range (m₁ * m₂ - 1)).map fun k => liftPrefix m₁ M (k + 1) - liftPrefix m₁ M k

theorem liftPrefix_strictMono {m₁ M : ℕ} (hm₁ : 0 < m₁) (hM : m₁ ≤ M) :
    StrictMono (liftPrefix m₁ M) := by
  refine strictMono_nat_of_lt_succ fun L => ?_
  have hdm : L % m₁ + m₁ * (L / m₁) = L := Nat.mod_add_div L m₁
  have hmod : L % m₁ < m₁ := Nat.mod_lt L hm₁
  unfold liftPrefix
  rcases Nat.lt_or_ge (L % m₁ + 1) m₁ with h | h
  · obtain ⟨h1, h2⟩ := (Nat.div_mod_unique hm₁).2
      ⟨(by omega : L % m₁ + 1 + m₁ * (L / m₁) = L + 1), h⟩
    rw [h1, h2]
    omega
  · obtain ⟨h1, h2⟩ := (Nat.div_mod_unique hm₁).2
      ⟨(by rw [Nat.mul_add_one]; omega : 0 + m₁ * (L / m₁ + 1) = L + 1), hm₁⟩
    rw [h1, h2, Nat.mul_add_one]
    omega

@[simp] theorem liftSeq_length (m₁ m₂ M : ℕ) : (liftSeq m₁ m₂ M).length = m₁ * m₂ - 1 := by
  simp [liftSeq]

theorem liftSeq_pos {m₁ m₂ M : ℕ} (hm₁ : 0 < m₁) (hM : m₁ ≤ M) :
    ∀ a ∈ liftSeq m₁ m₂ M, 0 < a := by
  intro a ha
  simp only [liftSeq, List.mem_map, List.mem_range] at ha
  obtain ⟨k, -, rfl⟩ := ha
  have := liftPrefix_strictMono hm₁ hM (show k < k + 1 by omega)
  omega

theorem liftSeq_take_sum {m₁ m₂ M : ℕ} (hm₁ : 0 < m₁) (hM : m₁ ≤ M) {L : ℕ}
    (hL : L ≤ m₁ * m₂ - 1) : ((liftSeq m₁ m₂ M).take L).sum = liftPrefix m₁ M L := by
  have hmono := (liftPrefix_strictMono hm₁ hM).monotone
  have key : ∀ n, ((List.range n).map
      fun k => liftPrefix m₁ M (k + 1) - liftPrefix m₁ M k).sum = liftPrefix m₁ M n := by
    intro n
    induction n with
    | zero => simp [liftPrefix]
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      have := hmono (show n ≤ n + 1 by omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  rw [liftSeq, ← List.map_take, List.take_range, Nat.min_eq_left hL, key]

/-- With `M = 3m₁ − 2` every prefix of `liftSeq` has average at most 3. -/
theorem liftPrefix_le_three_mul (m₁ L : ℕ) :
    liftPrefix m₁ (3 * m₁ - 2) L ≤ 3 * L := by
  unfold liftPrefix
  have hdm := Nat.mod_add_div L m₁
  have : (3 * m₁ - 2) * (L / m₁) ≤ 3 * (m₁ * (L / m₁)) :=
    calc (3 * m₁ - 2) * (L / m₁) ≤ (3 * m₁) * (L / m₁) :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = 3 * (m₁ * (L / m₁)) := by ring
  omega

/-- The cover of Lemma 4.1: a cover of the nonzero elements of
`ℤ_{m₁} × ℤ_{m₂}` by `q` sets that are sumfree in the group gives a cover of
the block sums of `liftSeq m₁ m₂ M` by `q` sumfree sets. -/
theorem coveredBySumFree_liftSeq {m₁ m₂ q M : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hM : 3 * m₁ - 2 ≤ M) (C : Fin q → Set (ZMod m₁ × ZMod m₂))
    (hC : ∀ i, GroupSumFree (C i)) (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) :
    CoveredBySumFree (blockSums (liftSeq m₁ m₂ M)) q := by
  classical
  have hM' : m₁ ≤ M := by omega
  -- Each block sum `d` has a form `d = r + M e` with `|r| < m₁`, `0 ≤ e < m₂`,
  -- and `r > 0` when `e = 0`.
  have hrep : ∀ d : ℕ, ∃ re : ℤ × ℤ, d ∈ blockSums (liftSeq m₁ m₂ M) →
      (d : ℤ) = re.1 + M * re.2 ∧ -(m₁ : ℤ) < re.1 ∧ re.1 < m₁ ∧ 0 ≤ re.2 ∧ re.2 < m₂ ∧
        (re.2 = 0 → 0 < re.1) := by
    intro d
    by_cases hd : d ∈ blockSums (liftSeq m₁ m₂ M)
    swap
    · exact ⟨(0, 0), fun h => absurd h hd⟩
    obtain ⟨a, b, hab, hb, rfl⟩ := exists_of_mem_blockSums hd
    rw [liftSeq_length] at hb
    rw [liftSeq_take_sum hm₁ hM' hb, liftSeq_take_sum hm₁ hM' (by omega)]
    have hpab := liftPrefix_strictMono hm₁ hM' hab
    refine ⟨(((b % m₁ : ℕ) : ℤ) - ((a % m₁ : ℕ) : ℤ), ((b / m₁ : ℕ) : ℤ) - ((a / m₁ : ℕ) : ℤ)),
      fun _ => ?_⟩
    have hja : a / m₁ ≤ b / m₁ := Nat.div_le_div_right hab.le
    have hjb : b / m₁ < m₂ := (Nat.div_lt_iff_lt_mul hm₁).2 (by
      have : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
      rw [Nat.mul_comm]; omega)
    have hua := Nat.mod_lt a hm₁
    have hub := Nat.mod_lt b hm₁
    have hda := Nat.mod_add_div a m₁
    have hdb := Nat.mod_add_div b m₁
    unfold liftPrefix at hpab ⊢
    generalize a % m₁ = ua at hua hda hpab ⊢
    generalize b % m₁ = ub at hub hdb hpab ⊢
    generalize a / m₁ = ja at hja hda hpab ⊢
    generalize b / m₁ = jb at hja hjb hdb hpab ⊢
    refine ⟨?_, by omega, by omega, by omega, by omega, fun he => ?_⟩
    · rw [Nat.cast_sub hpab.le]
      push_cast
      ring
    · have : ja = jb := by omega
      subst this
      omega
  choose ρ hρ using hrep
  let π : ℕ → ZMod m₁ × ZMod m₂ := fun d => (((ρ d).1 : ZMod m₁), ((ρ d).2 : ZMod m₂))
  -- `π` sends block sums to nonzero elements.
  have hπ0 : ∀ d ∈ blockSums (liftSeq m₁ m₂ M), π d ≠ 0 := by
    intro d hd h0
    obtain ⟨-, -, hr2, he1, he2, hpos⟩ := hρ d hd
    obtain ⟨h1, h2⟩ := Prod.mk_eq_zero.mp h0
    rw [CharP.intCast_eq_zero_iff (ZMod m₂) m₂] at h2
    have hr := hpos (Int.eq_zero_of_dvd_of_nonneg_of_lt he1 (by exact_mod_cast he2) h2)
    rw [CharP.intCast_eq_zero_iff (ZMod m₁) m₁] at h1
    have := Int.eq_zero_of_dvd_of_nonneg_of_lt hr.le (by exact_mod_cast hr2) h1
    omega
  -- `π` sends a sum of block sums to the sum in the group.
  have hadd : ∀ x ∈ blockSums (liftSeq m₁ m₂ M), ∀ y ∈ blockSums (liftSeq m₁ m₂ M),
      x + y ∈ blockSums (liftSeq m₁ m₂ M) → π x + π y = π (x + y) := by
    intro x hx y hy hxy
    obtain ⟨hdx, hx1, hx2, -, -, -⟩ := hρ x hx
    obtain ⟨hdy, hy1, hy2, -, -, -⟩ := hρ y hy
    obtain ⟨hdz, hz1, hz2, -, -, -⟩ := hρ (x + y) hxy
    push_cast at hdz
    have hid : (ρ x).1 + (ρ y).1 - (ρ (x + y)).1 =
        M * ((ρ (x + y)).2 - (ρ x).2 - (ρ y).2) := by
      linear_combination hdz - hdx - hdy
    have hr : (ρ x).1 + (ρ y).1 - (ρ (x + y)).1 = 0 :=
      Int.eq_zero_of_abs_lt_dvd ⟨_, hid⟩ (abs_lt.mpr ⟨by omega, by omega⟩)
    rw [hr] at hid
    have he : (ρ (x + y)).2 = (ρ x).2 + (ρ y).2 := by
      rcases mul_eq_zero.mp hid.symm with h | h
      · omega
      · linarith
    have hr' : (ρ (x + y)).1 = (ρ x).1 + (ρ y).1 := by linarith
    simp only [π, Prod.mk_add_mk, hr', he, Int.cast_add]
  refine ⟨fun i => {d | d ∈ blockSums (liftSeq m₁ m₂ M) ∧ π d ∈ C i}, fun i => ?_, ?_⟩
  · rintro x ⟨hx, hxC⟩ y ⟨hy, hyC⟩ ⟨hxy, hxyC⟩
    rw [← hadd x hx y hy hxy] at hxyC
    exact hC i _ hxC _ hyC hxyC
  · intro d hd
    obtain ⟨i, hi⟩ := hcov (π d) (hπ0 d hd)
    exact Set.mem_iUnion.2 ⟨i, hd, hi⟩

/-- Lemma 4.1 of the paper. The sets `C i` need not be disjoint. -/
theorem lift_lemma {m₁ m₂ q M : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hq : 0 < q)
    (hM : 3 * m₁ - 2 ≤ M) (C : Fin q → Set (ZMod m₁ × ZMod m₂))
    (hC : ∀ i, GroupSumFree (C i)) (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) :
    (liftSeq m₁ m₂ M).length = m₁ * m₂ - 1 ∧ (∀ a ∈ liftSeq m₁ m₂ M, 0 < a) ∧
      sdeg (blockSums (liftSeq m₁ m₂ M)) ≤ q ∧
      ∀ L ≤ m₁ * m₂ - 1, ((liftSeq m₁ m₂ M).take L).sum = L % m₁ + M * (L / m₁) := by
  have hM' : m₁ ≤ M := by omega
  exact ⟨liftSeq_length .., liftSeq_pos hm₁ hM',
    sdeg_le_of_coveredBySumFree hq (coveredBySumFree_liftSeq hm₁ hm₂ hM C hC hcov),
    fun _ hL => liftSeq_take_sum hm₁ hM' hL⟩

/-- Corollary 4.2 of the paper: if the nonzero elements of `ℤ_{m₁} × ℤ_{m₂}`
are covered by `n − 1` sets that are sumfree in the group, then
`L(n) ≥ m₁m₂`. -/
theorem le_erL_of_groupPartition {n m₁ m₂ : ℕ} (hn : 3 ≤ n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (C : Fin (n - 1) → Set (ZMod m₁ × ZMod m₂)) (hC : ∀ i, GroupSumFree (C i))
    (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) : m₁ * m₂ ≤ erL n := by
  refine le_erL (by omega) fun L hL hP => ?_
  by_contra! hlt
  have hM' : m₁ ≤ 3 * m₁ - 2 := by omega
  set A := liftSeq m₁ m₂ (3 * m₁ - 2) with hA
  have hLA : L ≤ m₁ * m₂ - 1 := by omega
  set B := A.take L with hB
  have hBlen : B.length = L := by simp [hB, hA]; omega
  have hBpos : ∀ b ∈ B, 0 < b := fun b hb =>
    liftSeq_pos hm₁ hM' b (List.mem_of_mem_take hb)
  have havg : average B ≤ n := by
    rw [average_le_iff (by omega), hBlen, hB, hA, liftSeq_take_sum hm₁ hM' hLA]
    exact (liftPrefix_le_three_mul m₁ L).trans (Nat.mul_le_mul_right L (by omega))
  have hcovB : CoveredBySumFree (blockSums B) (n - 1) :=
    (coveredBySumFree_liftSeq hm₁ hm₂ le_rfl C hC hcov).mono
      (blockSums_mono_of_infix (List.take_prefix L A).isInfix)
  have h := (hP B hBlen hBpos havg).trans (sdeg_le_of_coveredBySumFree (by omega) hcovB)
  norm_cast at h
  omega

end ClassicalSchur
