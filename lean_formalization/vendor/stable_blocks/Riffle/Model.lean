import Riffle.Definitions

namespace Riffle

/-- W02/B01: the finite column total bounds every pile. -/
theorem count_le (D : Model) (i a : ℕ) (hi : i < D.K) (ha : a < D.k) :
    D.n i a ≤ D.N := by
  have h := Finset.single_le_sum (fun b (_ : b ∈ Finset.range D.k) => Nat.zero_le (D.n i b))
    (Finset.mem_range.mpr ha)
  simpa only [D.sum_counts i hi] using h

/-- W02/B01: zero piles do not prevent a legal next digit. -/
theorem exists_positive_digit (D : Model) (i : ℕ) (hi : i < D.K) :
    ∃ a, a < D.k ∧ 0 < D.n i a := by
  by_contra h
  have hz : ∀ a ∈ Finset.range D.k, D.n i a = 0 := by
    intro a ha
    have : ¬0 < D.n i a := fun hp => h ⟨a, Finset.mem_range.mp ha, hp⟩
    omega
  have hs := D.sum_counts i hi
  rw [Finset.sum_eq_zero hz] at hs
  have := D.one_lt_N
  omega

theorem prob_pos_iff (D : Model) (i a : ℕ) : 0 < prob D i a ↔ 0 < D.n i a := by
  have hn : (0 : NNReal) < D.N := by exact_mod_cast (lt_trans Nat.zero_lt_one D.one_lt_N)
  rw [prob, div_pos_iff_of_pos_right hn]
  exact Nat.cast_pos

theorem prob_le_one (D : Model) (i a : ℕ) (hi : i < D.K) (ha : a < D.k) :
    prob D i a ≤ 1 := by
  have hn : (0 : NNReal) < D.N := by exact_mod_cast (lt_trans Nat.zero_lt_one D.one_lt_N)
  rw [prob, div_le_one hn]
  exact_mod_cast count_le D i a hi ha

theorem sum_prob (D : Model) (i : ℕ) (hi : i < D.K) :
    ∑ a ∈ Finset.range D.k, prob D i a = 1 := by
  have hn : (D.N : NNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one D.one_lt_N))
  have hs : (∑ a ∈ Finset.range D.k, (D.n i a : NNReal)) = (D.N : NNReal) := by
    exact_mod_cast D.sum_counts i hi
  simp only [prob]
  rw [← Finset.sum_div, hs, div_self hn]

theorem largeDigits_nonempty {D : Model} (A : Setup D) (i : ℕ) (hi : i < D.K) :
    (largeDigits A i).Nonempty := by
  classical
  by_contra h
  have hsmall : ∀ a ∈ Finset.range D.k, (prob D i a : ℝ) < A.chi := by
    intro a ha
    by_contra hn
    exact h ⟨a, Finset.mem_filter.mpr ⟨ha, le_of_not_gt hn⟩⟩
  have hne : (Finset.range D.k).Nonempty := ⟨0, Finset.mem_range.mpr (by have := D.two_le_k; omega)⟩
  have hslt := Finset.sum_lt_sum_of_nonempty hne hsmall
  have hs : ∑ a ∈ Finset.range D.k, (prob D i a : ℝ) = 1 := by
    exact_mod_cast sum_prob D i hi
  have hk : (0 : ℝ) < D.k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) D.two_le_k)
  have hc := (lt_div_iff₀ hk).mp A.chi_lt
  simp only [hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hslt
  nlinarith

theorem leftIndex_mem {D : Model} (A : Setup D) (i : ℕ) (hi : i < D.K) :
    leftIndex A i ∈ largeDigits A i := by
  classical
  simp only [leftIndex, dif_pos (largeDigits_nonempty A i hi)]
  exact Finset.min'_mem _ _

theorem rightIndex_mem {D : Model} (A : Setup D) (i : ℕ) (hi : i < D.K) :
    rightIndex A i ∈ largeDigits A i := by
  classical
  simp only [rightIndex, dif_pos (largeDigits_nonempty A i hi)]
  exact Finset.max'_mem _ _

theorem leftIndex_legal {D : Model} (A : Setup D) (i : ℕ) (hi : i < D.K) :
    leftIndex A i < D.k ∧ 0 < D.n i (leftIndex A i) := by
  have h := Finset.mem_filter.mp (leftIndex_mem A i hi)
  refine ⟨Finset.mem_range.mp h.1, (prob_pos_iff D i _).mp ?_⟩
  exact_mod_cast lt_of_lt_of_le A.chi_pos h.2

theorem rightIndex_legal {D : Model} (A : Setup D) (i : ℕ) (hi : i < D.K) :
    rightIndex A i < D.k ∧ 0 < D.n i (rightIndex A i) := by
  have h := Finset.mem_filter.mp (rightIndex_mem A i hi)
  refine ⟨Finset.mem_range.mp h.1, (prob_pos_iff D i _).mp ?_⟩
  exact_mod_cast lt_of_lt_of_le A.chi_pos h.2

theorem leftIndex_le_rightIndex {D : Model} (A : Setup D) (i : ℕ) (hi : i < D.K) :
    leftIndex A i ≤ rightIndex A i := by
  classical
  unfold leftIndex
  rw [dif_pos (largeDigits_nonempty A i hi)]
  exact Finset.min'_le _ _ (rightIndex_mem A i hi)

/-- B01: digits outside the extreme large piles are genuinely small. -/
theorem prob_lt_chi_of_lt_left {D : Model} (A : Setup D) {i a : ℕ}
    (hi : i < D.K) (ha : a < D.k) (hleft : a < leftIndex A i) :
    (prob D i a : ℝ) < A.chi := by
  classical
  by_contra h
  have hm : a ∈ largeDigits A i := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr ha, le_of_not_gt h⟩
  have hle : leftIndex A i ≤ a := by
    rw [leftIndex, dif_pos (largeDigits_nonempty A i hi)]
    exact Finset.min'_le _ _ hm
  omega

theorem prob_lt_chi_of_right_lt {D : Model} (A : Setup D) {i a : ℕ}
    (hi : i < D.K) (ha : a < D.k) (hright : rightIndex A i < a) :
    (prob D i a : ℝ) < A.chi := by
  classical
  by_contra h
  have hm : a ∈ largeDigits A i := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr ha, le_of_not_gt h⟩
  have hle : a ≤ rightIndex A i := by
    rw [rightIndex, dif_pos (largeDigits_nonempty A i hi)]
    exact Finset.le_max' _ _ hm
  omega

end Riffle
