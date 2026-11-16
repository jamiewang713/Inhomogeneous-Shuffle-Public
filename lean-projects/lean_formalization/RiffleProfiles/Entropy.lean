import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite entropy estimates for frozen contracts F13--F15.

All support conditions concern positive counts only. In particular no
full-support assumption is made about a representative probability vector.
-/

open scoped BigOperators

namespace RiffleProfiles

variable {ι κ : Type*}

/-- Weighted finite entropy, with zero-count terms omitted. -/
noncomputable def profileEntropy (s : Finset ι) (c : ι → ℝ) : ℝ :=
  ∑ i ∈ s.filter (fun i => 0 < c i), c i * Real.log ((∑ j ∈ s, c j) / c i)

private theorem sum_positive_mul (s : Finset ι) (c f : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s.filter (fun i => 0 < c i), c i * f i) =
      ∑ i ∈ s, c i * f i := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpos : 0 < c i
  · simp [hpos]
  · have hz : c i = 0 := le_antisymm (le_of_not_gt hpos) (hc i hi)
    simp [hpos, hz]

private theorem sum_positive (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s.filter (fun i => 0 < c i), c i) = ∑ i ∈ s, c i := by
  simpa using sum_positive_mul s c (fun _ => 1) hc

/-- F13: finite Gibbs inequality, with positivity only on the support of `a`. -/
theorem finite_gibbs_inequality (s : Finset ι) (a w : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha_sum : ∑ i ∈ s, a i = 1)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (h_support : ∀ i ∈ s, 0 < a i → 0 < w i)
    (hw_sum : 0 < ∑ i ∈ s, w i) :
    (∑ i ∈ s.filter (fun i => 0 < a i), a i * Real.log (w i / a i)) ≤
      Real.log (∑ i ∈ s, w i) := by
  classical
  let W := ∑ i ∈ s, w i
  let t := s.filter (fun i => 0 < a i)
  have hW : 0 < W := hw_sum
  have hta : (∑ i ∈ t, a i) = 1 := (sum_positive s a ha).trans ha_sum
  have htw : (∑ i ∈ t, w i) ≤ W := by
    dsimp [t, W]
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hpos : 0 < a i
    · simp [hpos]
    · simp only [hpos, if_false]
      exact hw i hi
  have hterm : ∀ i ∈ t,
      a i * Real.log (w i / a i) ≤
        w i / W - a i + a i * Real.log W := by
    intro i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hai : 0 < a i := (Finset.mem_filter.mp hi).2
    have hwi : 0 < w i := h_support i his hai
    have hlog := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hwi (mul_pos hai hW))) hai.le
    have hlogid : Real.log (w i / a i) =
        Real.log (w i / (a i * W)) + Real.log W := by
      rw [Real.log_div hwi.ne' hai.ne',
        Real.log_div hwi.ne' (mul_ne_zero hai.ne' hW.ne'),
        Real.log_mul hai.ne' hW.ne']
      ring
    have hquot : a i * (w i / (a i * W) - 1) = w i / W - a i := by
      field_simp
      ring
    rw [hquot] at hlog
    rw [hlogid, mul_add]
    linarith
  have hsum := Finset.sum_le_sum hterm
  have hright : (∑ i ∈ t, (w i / W - a i + a i * Real.log W)) =
      (∑ i ∈ t, w i) / W - 1 + Real.log W := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_div, ← Finset.sum_mul, hta, one_mul]
  rw [hright] at hsum
  have hratio : (∑ i ∈ t, w i) / W ≤ 1 := (div_le_one hW).2 htw
  change (∑ i ∈ t, a i * Real.log (w i / a i)) ≤ Real.log W
  linarith

/-- The zero-total case of the weighted entropy definition. -/
theorem profileEntropy_eq_zero_of_sum_eq_zero (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hzero : ∑ i ∈ s, c i = 0) :
    profileEntropy s c = 0 := by
  classical
  have hi_zero : ∀ i ∈ s, c i = 0 := by
    intro i hi
    have hle := Finset.single_le_sum hc hi
    rw [hzero] at hle
    exact le_antisymm hle (hc i hi)
  unfold profileEntropy
  apply Finset.sum_eq_zero
  intro i hi
  rw [hi_zero i (Finset.mem_filter.mp hi).1, zero_mul]

/-- F14: the tilted finite entropy bound, including zero total count. -/
theorem entropy_le_tilted_cost (s : Finset ι) (c p : ι → ℝ) (θ : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hp : ∀ i ∈ s, 0 ≤ p i)
    (h_support : ∀ i ∈ s, 0 < c i → 0 < p i)
    (_hθ : 0 < θ) (hZ : 0 < ∑ i ∈ s, (p i) ^ θ) :
    profileEntropy s c ≤
      θ * (∑ i ∈ s, c i * (-Real.log (p i))) +
        (∑ i ∈ s, c i) * Real.log (∑ i ∈ s, (p i) ^ θ) := by
  classical
  let C := ∑ i ∈ s, c i
  have hC_nonneg : 0 ≤ C := Finset.sum_nonneg hc
  by_cases hC_zero : C = 0
  · have hc_zero : ∀ i ∈ s, c i = 0 := by
      intro i hi
      have hle : c i ≤ C := Finset.single_le_sum hc hi
      rw [hC_zero] at hle
      exact le_antisymm hle (hc i hi)
    have hcost_zero : (∑ i ∈ s, c i * (-Real.log (p i))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hc_zero i hi, zero_mul]
    rw [profileEntropy_eq_zero_of_sum_eq_zero s c hc hC_zero, hcost_zero]
    change 0 ≤ θ * 0 + C * Real.log (∑ i ∈ s, p i ^ θ)
    simp [hC_zero]
  · have hC : 0 < C := lt_of_le_of_ne hC_nonneg (Ne.symm hC_zero)
    have hnorm_nonneg : ∀ i ∈ s, 0 ≤ c i / C :=
      fun i hi => div_nonneg (hc i hi) hC.le
    have hnorm_sum : (∑ i ∈ s, c i / C) = 1 := by
      rw [← Finset.sum_div]
      exact div_self hC.ne'
    have hpower_nonneg : ∀ i ∈ s, 0 ≤ p i ^ θ :=
      fun i hi => Real.rpow_nonneg (hp i hi) θ
    have hpower_support : ∀ i ∈ s, 0 < c i / C → 0 < p i ^ θ := by
      intro i hi hci
      exact Real.rpow_pos_of_pos
        (h_support i hi ((div_pos_iff_of_pos_right hC).mp hci)) θ
    have hg := finite_gibbs_inequality s (fun i => c i / C) (fun i => p i ^ θ)
      hnorm_nonneg hnorm_sum hpower_nonneg hpower_support hZ
    simp only [div_pos_iff_of_pos_right hC] at hg
    have hg_mul := mul_le_mul_of_nonneg_left hg hC.le
    have hidentity : profileEntropy s c =
        C * (∑ i ∈ s.filter (fun i => 0 < c i),
          (c i / C) * Real.log (p i ^ θ / (c i / C))) +
        θ * (∑ i ∈ s, c i * (-Real.log (p i))) := by
      rw [← sum_positive_mul s c (fun i => -Real.log (p i)) hc]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      unfold profileEntropy
      apply Finset.sum_congr rfl
      intro i hi
      have his : i ∈ s := (Finset.mem_filter.mp hi).1
      have hci : 0 < c i := (Finset.mem_filter.mp hi).2
      have hpi : 0 < p i := h_support i his hci
      change c i * Real.log (C / c i) = _
      rw [Real.log_div hC.ne' hci.ne',
        Real.log_div (Real.rpow_pos_of_pos hpi θ).ne' (div_ne_zero hci.ne' hC.ne'),
        Real.log_rpow hpi θ, Real.log_div hci.ne' hC.ne']
      field_simp
      ring
    rw [hidentity]
    change C * _ + θ * _ ≤ θ * _ + C * _
    linarith

/-- F15: sum the tilted entropy inequality over a finite family of cells. -/
theorem profile_entropy_le (cells : Finset κ) (digits : Finset ι)
    (c p : κ → ι → ℝ) (θ : ℝ)
    (hc : ∀ q ∈ cells, ∀ i ∈ digits, 0 ≤ c q i)
    (hp : ∀ q ∈ cells, ∀ i ∈ digits, 0 ≤ p q i)
    (h_support : ∀ q ∈ cells, ∀ i ∈ digits, 0 < c q i → 0 < p q i)
    (hθ : 0 < θ)
    (hZ : ∀ q ∈ cells, 0 < ∑ i ∈ digits, p q i ^ θ) :
    (∑ q ∈ cells, profileEntropy digits (c q)) ≤
      θ * (∑ q ∈ cells, ∑ i ∈ digits, c q i * (-Real.log (p q i))) -
        ∑ q ∈ cells, (∑ i ∈ digits, c q i) *
          (-Real.log (∑ i ∈ digits, p q i ^ θ)) := by
  have hsum := Finset.sum_le_sum (fun q hq =>
    entropy_le_tilted_cost digits (c q) (p q) θ
      (hc q hq) (hp q hq) (h_support q hq) hθ (hZ q hq))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_neg,
    Finset.sum_neg_distrib, sub_neg_eq_add] using hsum

/-- F15: deleting exceptional positions has exactly their normalized cost. -/
theorem exceptional_cost_identity [DecidableEq ι] (positions exceptional : Finset ι)
    (hsubset : exceptional ⊆ positions) (ψ : ι → ℝ) (L : ℝ) :
    (∑ i ∈ positions, ψ i) / L - (∑ i ∈ positions \ exceptional, ψ i) / L =
      (∑ i ∈ exceptional, ψ i) / L := by
  rw [← Finset.sum_sdiff hsubset, add_div]
  ring

/-- F15: a bounded nonnegative cost loses at most `M |E| / L`. -/
theorem exceptional_cost_bounds [DecidableEq ι] (positions exceptional : Finset ι)
    (hsubset : exceptional ⊆ positions) (ψ : ι → ℝ) (L M : ℝ)
    (hL : 0 < L) (hψ_nonneg : ∀ i ∈ positions, 0 ≤ ψ i)
    (hψ_bound : ∀ i ∈ positions, ψ i ≤ M) :
    0 ≤ (∑ i ∈ positions, ψ i) / L -
        (∑ i ∈ positions \ exceptional, ψ i) / L ∧
    (∑ i ∈ positions, ψ i) / L -
        (∑ i ∈ positions \ exceptional, ψ i) / L ≤
      M * (exceptional.card : ℝ) / L := by
  rw [exceptional_cost_identity positions exceptional hsubset ψ L]
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i hi => hψ_nonneg i (hsubset hi))) hL.le
  · apply div_le_div_of_nonneg_right _ hL.le
    calc
      (∑ i ∈ exceptional, ψ i) ≤ ∑ _i ∈ exceptional, M :=
        Finset.sum_le_sum (fun i hi => hψ_bound i (hsubset hi))
      _ = M * (exceptional.card : ℝ) := by simp [mul_comm]

/-- F15: combine the entropy estimate, deletion loss, and any proved finite
cell-replacement error. No target is identified with an integral here. -/
theorem entropy_error_of_replacement (H S θ good all target error loss : ℝ)
    (hentropy : H ≤ θ * S - good)
    (hdeletion : all - good ≤ loss)
    (hreplacement : |all - target| ≤ error) :
    H ≤ θ * S - target + error + loss := by
  have hlower := (abs_le.mp hreplacement).1
  linarith

end RiffleProfiles
