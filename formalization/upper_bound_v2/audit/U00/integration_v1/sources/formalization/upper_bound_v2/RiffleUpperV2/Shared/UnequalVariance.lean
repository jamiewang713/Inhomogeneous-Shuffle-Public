import RiffleUpperV2.Anchor.VarianceAlgebra

noncomputable section
namespace RiffleUpperV2
open RiffleLowerV2.Thinning.Compat

/-- Scalar count calculation for an unequal reveal. The reserve bound forces
a positive sample complement; population at least two is a conclusion. -/
theorem unequalVarianceFromCounts (P : HypergeomParams) {n A M w p q g : ℝ}
    (hn : 0 < n) (hA : 0 ≤ A) (hw : 0 < w)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hg : 0 < g)
    (hreserve : M ≤ (1-g)*n)
    (hpop : (P.population : ℝ) = n-A)
    (htotal : A + P.draws ≤ M) (hdraw : w/2 ≤ P.draws)
    (hmark : p/2 ≤ (P.marked : ℝ)/P.population)
    (hunmark : q/2 ≤ ((P.population : ℝ)-P.marked)/P.population) :
    g*w*p*q/8 ≤ P.varianceFormula := by
  have hdpos : (0 : ℝ) < P.draws := lt_of_lt_of_le (by positivity) hdraw
  have hNpos : (0 : ℝ) < P.population := hdpos.trans_le (by exact_mod_cast P.draws_le)
  have hcomp : g*(P.population : ℝ) ≤ (P.population : ℝ)-P.draws := by
    rw [hpop]
    nlinarith [mul_nonneg hg.le hA]
  have hcpos : 0 < (P.population : ℝ)-P.draws :=
    lt_of_lt_of_le (mul_pos hg hNpos) hcomp
  have hN : 2 ≤ P.population := by
    have hd : 0 < P.draws := by exact_mod_cast hdpos
    have hc : P.draws < P.population := by exact_mod_cast (sub_pos.mp hcpos)
    omega
  have hv := Anchor.variance_from_fraction_bounds P hN
    (by positivity : 0 ≤ p/2) (by positivity : 0 ≤ q/2) hg.le
    hmark hunmark ((le_div_iff₀ hNpos).mpr hcomp)
  have hh := mul_le_mul_of_nonneg_right hdraw
    (by positivity : 0 ≤ (p/2)*(q/2)*g)
  calc
    g*w*p*q/8 = (w/2)*((p/2)*(q/2)*g) := by ring
    _ ≤ (P.draws : ℝ)*((p/2)*(q/2)*g) := hh
    _ = (P.draws : ℝ)*(p/2)*(q/2)*g := by ring
    _ ≤ P.varianceFormula := hv

/-- A witness-cylinder mean and the opposite-side mass bound give the
product of the two extremal side means, without choosing their order. -/
theorem witnessVarianceProduct {w d p q ell r M g : ℝ}
    (hw : 0 ≤ w) (hd : 0 ≤ d) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hM : 0 < M) (hg : 0 ≤ g)
    (hwd : w*d = ell) (hdp : d ≤ p) (hrq : r/M ≤ q) :
    g*ell*r/(8*M) ≤ g*w*p*q/8 := by
  have hprod : ell*(r/M) ≤ (w*p)*q := by
    rw [← hwd]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hdp hw) hrq
      (div_nonneg hr hM.le) (mul_nonneg hw hp)
  have hh := mul_le_mul_of_nonneg_left hprod hg
  calc
    g*ell*r/(8*M) = g*(ell*(r/M))/8 := by ring
    _ ≤ g*((w*p)*q)/8 := div_le_div_of_nonneg_right hh (by norm_num)
    _ = _ := by ring

/-- The side-mass partition converts the symmetric product estimate to
the smaller side. Neither side needs to be at least one. -/
theorem varianceSideMinimum {ell r M D g : ℝ}
    (hell : 0 < ell) (hr : 0 < r) (hM : 0 < M) (hD : 0 < D)
    (hg : 0 ≤ g) (hbound : M ≤ D*max ell r) :
    g*min ell r/(8*D) ≤ g*ell*r/(8*M) := by
  have hs : min ell r * M ≤ D*ell*r := by
    have hh := mul_le_mul_of_nonneg_left hbound (le_min hell.le hr.le)
    rcases le_total ell r with h | h
    · simp only [min_eq_left h, max_eq_right h] at hh ⊢
      nlinarith [hh]
    · simp only [min_eq_right h, max_eq_left h] at hh ⊢
      nlinarith [hh]
  apply (div_le_div_iff₀ (by positivity : 0 < 8*D) (by positivity : 0 < 8*M)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hs hg]

end RiffleUpperV2
