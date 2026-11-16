import RiffleLowerV2.Ascent.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter
open scoped Topology
namespace RiffleLowerV2.Ascent

/-- An explicit mass threshold dominates both the clipping and test losses. -/
theorem lalley_gap {M D δ r d : ℝ} (hM : 0 < M)
    (hsize : 576 ≤ M^δ) (hD : 24*D ≤ M^δ)
    (hr : M^(1/2+δ) ≤ r) (hd : d ≤ D * Real.sqrt M) :
    M^(1/2+δ)/12 ≤ r/6-d-M^(1/2+δ/2) := by
  let z := M^(δ/2)
  have hz : 0 ≤ z := Real.rpow_nonneg hM.le _
  have hzsq : z^2 = M^δ := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1
    norm_num
  have hz24 : 24 ≤ z := by nlinarith
  have hzbound : D+z ≤ z^2/12 := by rw [← hzsq] at hD; nlinarith
  have hmul := mul_le_mul_of_nonneg_left hzbound (Real.rpow_nonneg hM.le (1/2 : ℝ))
  have hfull : M^(1/2+δ) = M^(1/2 : ℝ) * z^2 := by rw [Real.rpow_add hM, hzsq]
  have hhalf : M^(1/2+δ/2) = M^(1/2 : ℝ) * z := Real.rpow_add hM _ _
  rw [Real.sqrt_eq_rpow] at hd
  rw [hfull] at hr ⊢
  rw [hhalf]
  nlinarith

theorem lalley_gap_square {M δ : ℝ} (hM : 0 < M) :
    (M^(1/2+δ)/12)^2/M = M^(2*δ)/144 := by
  have hp : (M^(1/2+δ))^2 = M * M^(2*δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    have he : (1/2+δ)*(2:ℝ) = 1+2*δ := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he, Real.rpow_add hM, Real.rpow_one]
  rw [div_pow, hp]
  field_simp
  ring

/-- Quantitative conditional failure, uniform over the deck, graph and clipped set. -/
theorem quantitative_component_failure (hc : Targets.ComponentComparison)
    {N : ℕ} (G : PathEdges N) (H : Finset (Fin N)) {M D δ : ℝ}
    (hM : 0 < M) (hHM : (H.card : ℝ) ≤ M)
    (hsize : 576 ≤ M^δ) (hD : 24*D ≤ M^δ)
    (hr : M^(1/2+δ) ≤ ((G ∩ internalEdges H).card : ℝ))
    (hd : ((boundary H).card : ℝ) ≤ D * Real.sqrt M) :
    probability (uniformPermutation N) (fun π =>
      (ascentCount H (componentSort G π) : ℝ) ≤
        ((internalEdges H).card : ℝ)/2+M^(1/2+δ/2)) ≤
      Real.exp (-M^(2*δ)/144) := by
  have hgap := lalley_gap hM hsize hD hr hd
  have hpositive : 0 < M^(1/2+δ)/12 := div_pos (Real.rpow_pos_of_pos hM _) (by norm_num)
  have ht := hc N G H M (M^(1/2+δ/2)) hM hHM
    (Real.rpow_pos_of_pos hM _) (hpositive.trans_le hgap)
  refine ht.trans (Real.exp_le_exp.mpr ?_)
  have hs := sq_le_sq₀ hpositive.le (hpositive.trans_le hgap).le |>.mpr hgap
  have hdiv := div_le_div_of_nonneg_right hs hM.le
  rw [lalley_gap_square hM] at hdiv
  simpa only [neg_div] using neg_le_neg hdiv

end RiffleLowerV2.Ascent
