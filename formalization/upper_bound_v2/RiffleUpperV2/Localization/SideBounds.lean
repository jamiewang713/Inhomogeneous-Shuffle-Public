import RiffleUpperV2.Localization.SidePieces

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor Hypergeometric

def sideMaximum {k n d : ℕ} (s : SuffixSide) (cuts : Cuts k n d)
    (R : Finset (Fin n)) (v : Prefix k d) : ℝ :=
  match s with | .lower => leftScale cuts R v | .upper => rightScale cuts R v

theorem sideMean_nonnegative {k n d : ℕ} (s : SuffixSide) (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val) :
    0 ≤ sideMean s cuts R x i := by
  cases s
  · exact leftMean_nonneg cuts R x i
  · exact rightMean_nonneg cuts R x i

theorem sideMean_le_prefixMean {k n d : ℕ} (s : SuffixSide) (cuts : Cuts k n d)
    (hn : 0 < n) (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val) :
    sideMean s cuts R x i ≤ anchoredMean cuts R (takePrefix x i.val i.isLt.le) := by
  rw [← sideMean_eq_cylinderMean cuts hn s R x i]
  unfold cylinderMean
  rw [prefixThenDigits_mass cuts hn, sidePrefixMass_eq]
  have hfrac : (allowedCount cuts (prefixColumn x i) (s.strictDigits (x.2.get i)) : ℝ) / n ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    exact_mod_cast allowedCount_le cuts (prefixColumn x i) (s.strictDigits (x.2.get i))
  have hmass : 0 ≤ prefixMass cuts (takePrefix x i.val i.isLt.le) := by
    exact Finset.prod_nonneg (fun _ _ => by positivity)
  unfold anchoredMean
  nlinarith [mul_le_mul_of_nonneg_left hfrac
    (mul_nonneg (Nat.cast_nonneg R.card) hmass)]

theorem sideMean_before_join {k n d : ℕ} (s : SuffixSide) (cuts : Cuts k n d)
    (R : Finset (Fin n)) {v x : Prefix k d} (hvx : IsPrefix v x)
    (i : Fin x.1.val) (hi : i.val < v.1.val) :
    sideMean s cuts R x i ≤ sideMaximum s cuts R v := by
  let j : Fin v.1.val := ⟨i.val,hi⟩
  have he : extendIndex hvx j = i := Fin.ext rfl
  have h := sideMeans_extension cuts R hvx j
  rw [he] at h
  cases s
  · exact h.1.le.trans (leftMean_le_scale cuts R v j)
  · exact h.2.le.trans (rightMean_le_scale cuts R v j)

theorem sideMean_after_join {k n d : ℕ} (s : SuffixSide) (cuts : Cuts k n d)
    (hn : 0 < n) (R : Finset (Fin n)) {v x : Prefix k d} (hvx : IsPrefix v x)
    (i : Fin x.1.val) (hi : v.1.val ≤ i.val) :
    sideMean s cuts R x i ≤ anchoredMean cuts R v := by
  apply (sideMean_le_prefixMean s cuts hn R x i).trans
  apply anchoredMean_antitone cuts hn R
  exact List.prefix_of_prefix_length_le hvx (takePrefix_isPrefix _ _ _)
    (by rw [List.Vector.toList_length, List.Vector.toList_length]; exact hi)

/-- Every count in the smaller-side endpoint expansion has mean at most χ⁻¹ω.
No size lower bound or reserve assumption is used. -/
theorem smallerSide_mean_bound {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) {χ : ℝ} {y z v x : Prefix k d}
    (hpair : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x) :
    ∃ s : SuffixSide,
      (∀ i : Fin x.1.val, sideMean s cuts R x i ≤ χ⁻¹ * sideScale cuts R v) ∧
      anchoredMean cuts R x ≤ χ⁻¹ * sideScale cuts R v := by
  have hc := (genuine_sideScale_pos cuts hn R hpair).2
  have hω : 0 < sideScale cuts R v :=
    (genuine_sideScale_pos cuts hn R hpair).1.trans_le hc
  have hmean : anchoredMean cuts R v ≤ χ⁻¹ * sideScale cuts R v := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hpair.chi_pos).mpr (by simpa [mul_comm] using hc)
  have hωB : sideScale cuts R v ≤ χ⁻¹ * sideScale cuts R v := by
    have hi : 1 ≤ χ⁻¹ := (one_le_inv₀ hpair.chi_pos).mpr hpair.chi_lt_one.le
    nlinarith
  have hs : ∃ s, sideMaximum s cuts R v = sideScale cuts R v := by
    rcases le_total (leftScale cuts R v) (rightScale cuts R v) with h | h
    · exact ⟨.lower, (min_eq_left h).symm⟩
    · exact ⟨.upper, (min_eq_right h).symm⟩
  obtain ⟨s,hs⟩ := hs
  refine ⟨s,?_,(anchoredMean_antitone cuts hn R hvx).trans hmean⟩
  intro i
  by_cases hi : i.val < v.1.val
  · have hh := sideMean_before_join s cuts R hvx i hi
    rw [hs] at hh
    exact hh.trans hωB
  · exact (sideMean_after_join s cuts hn R hvx i (le_of_not_gt hi)).trans hmean

end RiffleUpperV2.Localization
