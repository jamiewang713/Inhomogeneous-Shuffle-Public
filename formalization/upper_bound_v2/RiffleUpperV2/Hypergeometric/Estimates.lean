import RiffleUpperV2.Hypergeometric.AntiConcentration
import RiffleLowerV2.Thinning.Compat.HypergeometricConcentration
import RiffleLowerV2.Thinning.Recursion
import RiffleLowerV2.Thinning.Tails

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Hypergeometric
open RiffleLowerV2 RiffleLowerV2.Thinning RiffleLowerV2.Thinning.Compat

/-- The existing finite law and primary PMF API have identical expectations. -/
theorem finiteLaw_expect {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) :
    expect P.toPMF f = P.expect f := by
  simp only [expect, FiniteLaw.expect, FiniteLaw.toPMF_toReal]

theorem finiteLaw_probability {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (E : Ω → Prop) :
    probability P.toPMF E = P.prob E := by
  classical
  simp only [probability, expect, FiniteLaw.prob, FiniteLaw.toPMF_toReal]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

/-- Exact hypergeometric domination for every positive power parameter. -/
theorem transformBound (p : Compat.HypergeomParams) (s : ℝ) (hs : 0 < s) :
    expect p.law.toPMF (fun q => s ^ q.val) ≤
      (1 - (p.draws : ℝ) / p.population + (p.draws : ℝ) / p.population * s) ^ p.marked ∧
    (1 - (p.draws : ℝ) / p.population + (p.draws : ℝ) / p.population * s) ^ p.marked ≤
      Real.exp (p.mean * (s - 1)) := by
  have hq0 : 0 ≤ (p.draws : ℝ) / p.population := by positivity
  have hq1 : (p.draws : ℝ) / p.population ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast p.draws_le) (by positivity)
  refine ⟨?_, ?_⟩
  · rw [finiteLaw_expect]
    exact p.expect_pow_le_all hs
  · have h := binomial_le_exp (M := p.marked) hq0 hq1 hs
    simpa only [Compat.HypergeomParams.mean, mul_div_assoc] using h

/-- Equivalent exponential-moment formulation, for every real exponential parameter. -/
theorem mgfBound (p : Compat.HypergeomParams) (z : ℝ) :
    expect p.law.toPMF (fun q => Real.exp (z * (q.val : ℝ))) ≤
      Real.exp (p.mean * (Real.exp z - 1)) := by
  have h := (transformBound p (Real.exp z) (Real.exp_pos z)).1.trans
    (transformBound p (Real.exp z) (Real.exp_pos z)).2
  simpa only [mul_comm z, Real.exp_nat_mul] using h

/-- Two-sided bound including zero variance and populations zero and one. -/
theorem twoSidedTail (p : Compat.HypergeomParams) {t : ℝ} (ht : 0 < t) :
    probability p.law.toPMF (fun q => t ≤ |(q.val : ℝ) - p.mean|) ≤
      2 * Real.exp (-t^2 / (4 * (p.mean + t))) :=
  bernstein_of_transform _ _ _ p.mean_nonneg
    (fun s hs => (transformBound p s hs).1.trans (transformBound p s hs).2) ht

/-- Explicit absolute atom constant; reciprocal square roots require positive variance. -/
theorem atomBound (p : Compat.HypergeomParams) (hv : 0 < p.varianceFormula) (z : ℕ) :
    probability p.law.toPMF (fun q => q.val = z) ≤ 4 / Real.sqrt p.varianceFormula := by
  rw [finiteLaw_probability]
  exact HypergeomParams.pointMass_le_four_div_sqrt p hv z

theorem exactMean (p : Compat.HypergeomParams) :
    expect p.law.toPMF (fun q => (q.val : ℝ)) = p.mean := by
  rw [finiteLaw_expect]
  exact p.expect_val

theorem exactVariance (p : Compat.HypergeomParams) :
    expect p.law.toPMF (fun q => ((q.val : ℝ) - p.mean)^2) = p.varianceFormula := by
  rw [finiteLaw_expect, ← p.expect_val]
  exact p.variance_val

/-- All zero-variance boundary cases are recorded separately from atomBound. -/
theorem zeroVariance_iff (p : Compat.HypergeomParams) :
    p.varianceFormula = 0 ↔ p.marked = 0 ∨ p.draws = 0 ∨
      p.marked = p.population ∨ p.draws = p.population := by
  rw [← p.variance_val]
  exact p.variance_eq_zero_iff

end RiffleUpperV2.Hypergeometric
