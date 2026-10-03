import RiffleUpperV2.Exponential.Numerical

noncomputable section
open scoped Topology
namespace RiffleUpperV2.Exponential
open Filter

/-- With fixed component/exploration constants, polynomial conditional tails and
vanishing single-matrix regularity failure make the quantitative criterion vanish. -/
theorem truncationRHS_tendsto (q C δ A : ℝ) (bound : ℕ)
    (hδ : 0 < δ) (hA : 0 < A) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.sqrt (2*q*C*(N : ℝ)^(-δ))/2 + r N +
      (N : ℝ)^(-A)/(bound+1).factorial) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^(-A)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hA).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hm : Tendsto (fun N : ℕ => 2*q*C*(N : ℝ)^(-δ)) atTop (𝓝 0) := by
    simpa using hp.const_mul (2*q*C)
  have hs : Tendsto (fun N : ℕ => Real.sqrt (2*q*C*(N : ℝ)^(-δ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hm
  simpa using ((hs.div_const 2).add hr).add (hpow.div_const ((bound+1).factorial : ℝ))

end RiffleUpperV2.Exponential
