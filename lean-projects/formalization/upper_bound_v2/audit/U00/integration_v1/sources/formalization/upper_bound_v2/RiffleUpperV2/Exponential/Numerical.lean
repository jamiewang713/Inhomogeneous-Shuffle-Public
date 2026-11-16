import RiffleUpperV2.Exponential.FiniteTV
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped BigOperators Topology
namespace RiffleUpperV2.Exponential
open Filter

/-- The source choice η B ≥ A+1 converts the actual occupancy tail into N^-A. -/
theorem component_power_bound {N B : ℕ} (hN : 1 ≤ N) {μ η A : ℝ}
    (hμ : 0 ≤ μ) (hmean : μ ≤ (N : ℝ)^(-η)) (hBA : A+1 ≤ η*B) :
    (N : ℝ)*μ^B ≤ (N : ℝ)^(-A) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  calc
    (N : ℝ)*μ^B ≤ (N : ℝ)*((N : ℝ)^(-η))^B :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ hmean B) hNp.le
    _ = (N : ℝ)^(1 + (-η)*(B : ℝ)) := by
      rw [← Real.rpow_mul_natCast hNp.le, Real.rpow_add hNp, Real.rpow_one]
    _ ≤ (N : ℝ)^(-A) := Real.rpow_le_rpow_of_exponent_le hNr (by nlinarith)

/-- An explicit finite-N denominator bound used after qγ ≤ 1/2. -/
theorem geometric_ratio_le_twice {q γ : ℝ} (hq : 0 ≤ q) (hγ : 0 ≤ γ)
    (hsmall : q*γ ≤ 1/2) : q*γ/(1-q*γ) ≤ 2*q*γ := by
  have hn : 0 ≤ q*γ := mul_nonneg hq hγ
  have hd : 0 < 1-q*γ := by linarith
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- With fixed q,C and δ>0 the geometric denominator is eventually at least 1/2.
The threshold is selected before the population N. -/
theorem eventually_geometricDenominator (q C δ : ℝ) (hδ : 0 < δ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, q*C*(N : ℝ)^(-δ) ≤ 1/2 := by
  have ht : Tendsto (fun N : ℕ => q*C*(N : ℝ)^(-δ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop hδ).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (q*C)
  have he := ht.eventually (eventually_lt_nhds (show (0 : ℝ) < 1/2 by norm_num))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp he
  refine ⟨max 2 N0, le_max_left _ _, fun N hN => ?_⟩
  exact (hN0 N ((le_max_right _ _).trans hN)).le

/-- The actual γ may be smaller than its polynomial envelope. -/
theorem geometric_ratio_le_power {N : ℕ} {q C δ γ : ℝ}
    (hq : 0 ≤ q) (hγ : 0 ≤ γ) (hγN : γ ≤ C*(N : ℝ)^(-δ))
    (hsmall : q*C*(N : ℝ)^(-δ) ≤ 1/2) :
    q*γ < 1 ∧ q*γ/(1-q*γ) ≤ 2*q*C*(N : ℝ)^(-δ) := by
  have hqγ : q*γ ≤ q*C*(N : ℝ)^(-δ) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hγN hq
  have hs : q*γ ≤ 1/2 := hqγ.trans hsmall
  refine ⟨by linarith, (geometric_ratio_le_twice hq hγ hs).trans ?_⟩
  nlinarith

end RiffleUpperV2.Exponential
