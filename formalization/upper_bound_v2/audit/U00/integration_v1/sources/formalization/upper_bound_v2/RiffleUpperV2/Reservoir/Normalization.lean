import RiffleUpperV2.Reservoir.ProductUpper

noncomputable section
namespace RiffleUpperV2.Reservoir

/-- The initial-pile normalization cancels in the source's correct direction,
including a zero pile or zero tail mass. -/
theorem initialPile_normalization {n r m : ℕ} (hn : 0<n) (hr : r≤n)
    {q α : ℝ} (hq : 0≤q) (hα0 : 0≤α) (hα1 : α≤1) :
    RiffleLowerV2.falling r m*q^((m:ℝ)*(1-α)) ≤
      (n:ℝ)^m * (((r:ℝ)/n)*q)^((m:ℝ)*(1-α)) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hp0 : 0≤(r:ℝ)/n := by positivity
  have hp1 : (r:ℝ)/n≤1 := (div_le_one hn0).mpr (by exact_mod_cast hr)
  have hpow : (r:ℝ)/n≤((r:ℝ)/n)^(1-α) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hp0 hp1
      (by linarith : 0≤1-α) (by linarith : 1-α≤1)
  have hfall : RiffleLowerV2.falling r m≤(r:ℝ)^m := by
    unfold RiffleLowerV2.falling
    exact_mod_cast Nat.descFactorial_le_pow r m
  have hscale : (r:ℝ)^m ≤ (n:ℝ)^m * ((r:ℝ)/n)^((m:ℝ)*(1-α)) := by
    have hh := pow_le_pow_left₀ hp0 hpow m
    have heq : (((r:ℝ)/n)^(1-α))^m=((r:ℝ)/n)^((m:ℝ)*(1-α)) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hp0]
      congr 1
      ring
    rw [heq] at hh
    have hl := mul_le_mul_of_nonneg_left hh (pow_nonneg hn0.le m)
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero m hn0.ne')] at hl
    exact hl
  apply (mul_le_mul_of_nonneg_right hfall (Real.rpow_nonneg hq _)).trans
  apply (mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hq _)).trans_eq
  rw [Real.mul_rpow hp0 hq]
  ring

end RiffleUpperV2.Reservoir
