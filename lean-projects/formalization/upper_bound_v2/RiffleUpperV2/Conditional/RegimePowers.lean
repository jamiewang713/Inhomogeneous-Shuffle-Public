import RiffleUpperV2.Conditional.Parameters

noncomputable section
namespace RiffleUpperV2.Conditional

/-- Exact normalization separating the ambient original-N multiplier from
mu=N*lambda; valid also at lambda=0. -/
theorem countPower_identity {N lam : ℝ} (hN : 0 < N) (hlam : 0 ≤ lam) (r α : ℝ) :
    N^r * lam^(r*(1-α)) = N^(r*α)*(N*lam)^(r*(1-α)) := by
  rw [Real.mul_rpow hN.le hlam]
  rw [← mul_assoc,← Real.rpow_add hN]
  congr 1
  ring

theorem tinyCount_power {N lam ξ α : ℝ} (hN : 0 < N) (hlam : 0 ≤ lam)
    (hα : α ≤ 1) (hμ : N*lam ≤ N^(-ξ)) :
    N*lam^(1-α) ≤ N^(-ξ+α*(1+ξ)) := by
  have he := countPower_identity hN hlam 1 α
  simp only [Real.rpow_one,one_mul] at he
  rw [he]
  calc
    _ ≤ N^α*(N^(-ξ))^(1-α) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hN.le hlam) hμ (by linarith)) (Real.rpow_nonneg hN.le _)
    _ = _ := by rw [← Real.rpow_mul hN.le,← Real.rpow_add hN]; congr 1; ring

/-- The near-unit estimate explicitly uses the remaining-tail factor. -/
theorem intermediateCollision_power {N lam qstar ξ η α tail : ℝ}
    (hN : 0 < N) (hlam : 0 ≤ lam) (hqstar : 0 ≤ qstar) (hα : α ≤ 1/2)
    (hμ : N*lam ≤ N^ξ) (hq : qstar ≤ N^(-η+ξ))
    (htail : tail ≤ qstar^(1-2*α)) :
    N^2 * lam^(2*(1-α))*tail ≤ N^(-η+3*ξ+2*α*(1+η-2*ξ)) := by
  have hnorm := countPower_identity hN hlam 2 α
  rw [Real.rpow_two] at hnorm
  rw [hnorm]
  calc
    _ ≤ (N^(2*α)*(N*lam)^(2*(1-α)))*(N^(-η+ξ))^(1-2*α) :=
      mul_le_mul_of_nonneg_left (htail.trans (Real.rpow_le_rpow hqstar hq (by linarith))) (by positivity)
    _ ≤ (N^(2*α)*(N^ξ)^(2*(1-α)))*(N^(-η+ξ))^(1-2*α) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (mul_nonneg hN.le hlam) hμ (by linarith)) (by positivity)
      · rfl
      · positivity
      · positivity
    _ = _ := by
      rw [← Real.rpow_mul hN.le,← Real.rpow_mul hN.le,← Real.rpow_add hN,← Real.rpow_add hN]
      congr 1
      ring

end RiffleUpperV2.Conditional
