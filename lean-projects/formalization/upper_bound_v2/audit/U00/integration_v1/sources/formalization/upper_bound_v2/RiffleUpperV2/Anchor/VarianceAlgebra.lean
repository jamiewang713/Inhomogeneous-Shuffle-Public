import RiffleUpperV2.Anchor.SourceSampling

noncomputable section
namespace RiffleUpperV2.Anchor
open RiffleLowerV2.Thinning.Compat

/-- Keep the sample-complement factor; the finite-population correction can
only increase the product when the population has at least two labels. -/
theorem variance_ge_fraction_product (P : HypergeomParams) (hN : 2 ≤ P.population) :
    (P.draws : ℝ) * ((P.marked : ℝ) / P.population) *
      (((P.population : ℝ) - P.marked) / P.population) *
      (((P.population : ℝ) - P.draws) / P.population) ≤ P.varianceFormula := by
  have hn : (0 : ℝ) < P.population := by exact_mod_cast (by omega : 0 < P.population)
  have hn₁ : (0 : ℝ) < (P.population : ℝ)-1 := by
    have : (2 : ℝ) ≤ P.population := by exact_mod_cast hN
    linarith
  have hm : (P.marked : ℝ) ≤ P.population := by exact_mod_cast P.marked_le
  have hd : (P.draws : ℝ) ≤ P.population := by exact_mod_cast P.draws_le
  let b : ℝ := (P.draws : ℝ) * ((P.marked : ℝ) / P.population) *
      (((P.population : ℝ) - P.marked) / P.population) *
      (((P.population : ℝ) - P.draws) / P.population)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 1 ≤ (P.population : ℝ) / ((P.population : ℝ)-1) := by
    apply (le_div_iff₀ hn₁).mpr
    linarith
  calc
    _ = b * 1 := by dsimp [b]; ring
    _ ≤ b * ((P.population : ℝ) / ((P.population : ℝ)-1)) :=
      mul_le_mul_of_nonneg_left hc hb
    _ = P.varianceFormula := by
      unfold b HypergeomParams.varianceFormula
      field_simp
      <;> ring

/-- The scalar step used on good reveal atoms. These are count/fraction
premises, not a probabilistic endpoint or anti-concentration premise. -/
theorem variance_from_fraction_bounds (P : HypergeomParams) (hN : 2 ≤ P.population)
    {a b g : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hm : a ≤ (P.marked : ℝ) / P.population)
    (hu : b ≤ ((P.population : ℝ)-P.marked) / P.population)
    (hc : g ≤ ((P.population : ℝ)-P.draws) / P.population) :
    (P.draws : ℝ) * a * b * g ≤ P.varianceFormula := by
  apply le_trans _ (variance_ge_fraction_product P hN)
  have hm₀ : 0 ≤ (P.marked : ℝ) / P.population := by positivity
  have hu₀ : 0 ≤ ((P.population : ℝ)-P.marked) / P.population := by
    apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast P.marked_le)
    · positivity
  have h₁ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg P.draws)
  have h₂ := mul_le_mul h₁ hu hb (mul_nonneg (Nat.cast_nonneg _) hm₀)
  exact mul_le_mul h₂ hc hg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hm₀) hu₀)

end RiffleUpperV2.Anchor
