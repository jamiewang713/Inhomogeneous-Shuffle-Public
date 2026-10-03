import RiffleUpperV2.Anchor.VarianceAlgebra

noncomputable section
namespace RiffleUpperV2.Anchor
open RiffleLowerV2.Thinning.Compat

theorem harmonic_side_min {a p q : ℝ} (ha : 0 ≤ a) (hp : 0 < p) (hq : 0 < q) :
    min (a*p) (a*q) ≤ 2*a*p*q/(p+q) := by
  have hs : 0 < p+q := add_pos hp hq
  rcases le_total p q with hpq | hqp
  · apply (min_le_left _ _).trans
    apply (le_div_iff₀ hs).mpr
    nlinarith [mul_nonneg (mul_nonneg ha hp.le) (sub_nonneg.mpr hpq)]
  · apply (min_le_right _ _).trans
    apply (le_div_iff₀ hs).mpr
    nlinarith [mul_nonneg (mul_nonneg ha hq.le) (sub_nonneg.mpr hqp)]

/-- Scalar finite-population calculation for the two-cylinder equal reveal.
Both positive draws and positive sample complement are derived from the
count lower bounds, so no variance positivity is assumed. -/
theorem equal_variance_from_counts (P : HypergeomParams) {n M a p q g : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hp : 0 < p) (hq : 0 < q) (hg : 0 < g)
    (hreserve : M ≤ (1-g)*n)
    (hpop : (P.population : ℝ) = n*(p+q)) (hmark : (P.marked : ℝ) = n*p)
    (hdraw : a*(p+q)/2 ≤ P.draws)
    (hcomp : (n-M)*(p+q)/2 ≤ (P.population : ℝ)-P.draws) :
    g * min (a*p) (a*q) / 8 ≤ P.varianceFormula := by
  have hs : 0 < p+q := add_pos hp hq
  have hN : (0 : ℝ) < P.population := by rw [hpop]; positivity
  have hdrawpos : (0 : ℝ) < P.draws := lt_of_lt_of_le (by positivity) hdraw
  have hres : 0 < n-M := by nlinarith [mul_pos hg hn]
  have hcomppos : 0 < (P.population : ℝ)-P.draws := lt_of_lt_of_le (by positivity) hcomp
  have hN₂ : 2 ≤ P.population := by
    have hd : 0 < P.draws := by exact_mod_cast hdrawpos
    have hdN : P.draws < P.population := by exact_mod_cast (sub_pos.mp hcomppos)
    omega
  have hmfrac : (P.marked : ℝ)/P.population = p/(p+q) := by
    rw [hmark, hpop]
    field_simp
  have hufrac : ((P.population : ℝ)-P.marked)/P.population = q/(p+q) := by
    rw [hmark, hpop]
    field_simp
    <;> ring
  have hcfrac : g/2 ≤ ((P.population : ℝ)-P.draws)/P.population := by
    apply (le_div_iff₀ hN).mpr
    rw [hpop]
    have ht : g*n ≤ n-M := by nlinarith [hreserve]
    nlinarith [mul_le_mul_of_nonneg_right ht hs.le]
  have hv := variance_from_fraction_bounds P hN₂ (by positivity : 0 ≤ p/(p+q))
    (by positivity : 0 ≤ q/(p+q)) (by positivity : 0 ≤ g/2)
    (le_of_eq hmfrac.symm) (le_of_eq hufrac.symm) hcfrac
  have hscale : a*p*q*g/(4*(p+q)) ≤
      (P.draws : ℝ)*(p/(p+q))*(q/(p+q))*(g/2) := by
    have hh := mul_le_mul_of_nonneg_right hdraw
      (by positivity : 0 ≤ (p/(p+q))*(q/(p+q))*(g/2))
    calc
      _ = (a*(p+q)/2)*((p/(p+q))*(q/(p+q))*(g/2)) := by field_simp [hs.ne'] <;> ring
      _ ≤ _ := by nlinarith [hh]
  have hmin := mul_le_mul_of_nonneg_left (harmonic_side_min ha.le hp hq) hg.le
  have hfinal : g*min (a*p) (a*q)/8 ≤ a*p*q*g/(4*(p+q)) := by
    have he : g*(2*a*p*q/(p+q))/8 = a*p*q*g/(4*(p+q)) := by field_simp [hs.ne'] <;> ring
    rw [← he]
    exact div_le_div_of_nonneg_right hmin (by norm_num)
  exact hfinal.trans (hscale.trans hv)

end RiffleUpperV2.Anchor
