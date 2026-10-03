import RiffleUpperV2.Anchor.EqualMeans
import RiffleUpperV2.Anchor.EqualVarianceAlgebra

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric

/-- The equal-case good cylinders force the actual conditional endpoint
variance to be large. No variance or endpoint concentration premise appears. -/
theorem endpointVariance_equal {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {g : ℝ}
    (hg : Reserve R g) (hl : 0 < leftMean cuts R x j) (hr : 0 < rightMean cuts R x j)
    (ω : Sample cuts) (hgood : equalGood cuts R x j ω) :
    g * min (leftMean cuts R x j) (rightMean cuts R x j) / 8 ≤
      (equalEndpointParams R x j ω).varianceFormula := by
  let a := (R.card : ℝ) * sidePrefixMass cuts x j
  let p := leftProbability cuts (prefixColumn x j) (x.2.get j)
  let q := rightProbability cuts (prefixColumn x j) (x.2.get j)
  let P := equalEndpointParams R x j ω
  have ha₀ : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (sidePrefixMass_nonneg cuts x j)
  have hp₀ : 0 ≤ p := by dsimp [p, leftProbability]; positivity
  have hq₀ : 0 ≤ q := by dsimp [q, rightProbability]; positivity
  have hl' : 0 < a*p := hl
  have hr' : 0 < a*q := hr
  have ha : 0 < a := by nlinarith
  have hp : 0 < p := by nlinarith
  have hq : 0 < q := by nlinarith
  have hparams := equalRevealParameters cuts (prefixColumn x j) (x.2.get j)
    (equalSampleRows R x j ω) ω (equalSampleRows_subset R x j ω)
  change P.population = _ ∧ P.marked = _ ∧ P.draws = _ at hparams
  have hcount := nonEqualCount cuts (prefixColumn x j) (x.2.get j)
  have hpopNat : P.population = allowedCount cuts (prefixColumn x j) (nonEqualDigits (x.2.get j)) := by
    rw [hparams.1]
    omega
  have hpop : (P.population : ℝ) = (n : ℝ)*(p+q) := by
    rw [hpopNat]
    have hh := nonEqualProbability cuts hn (prefixColumn x j) (x.2.get j)
    change (_ : ℝ) / n = p+q at hh
    have hn' : (n : ℝ) ≠ 0 := by positivity
    exact ((div_eq_iff hn').mp hh).trans (mul_comm _ _)
  have hmark : (P.marked : ℝ) = (n : ℝ)*p := by
    rw [hparams.2.1]
    dsimp [p, leftProbability]
    field_simp
  have hdraw : a*(p+q)/2 ≤ (P.draws : ℝ) := by
    rw [hparams.2.2]
    have hb := hgood.1
    rw [(equalCylinderMeans cuts hn R x j).1] at hb
    change (a*p+a*q)/2 ≤ _ at hb
    nlinarith
  have hcomp : ((n : ℝ)-R.card)*(p+q)/2 ≤ (P.population : ℝ)-P.draws := by
    have hc := hgood.2
    rw [(equalCylinderMeans cuts hn R x j).2] at hc
    change ((n : ℝ)-R.card)*(p+q)/2 ≤ _ at hc
    have hcard : ((equalSampleRows R x j ω).card : ℝ) + (equalReserveRows R x j ω).card ≤ P.population := by
      rw [hparams.1]
      exact_mod_cast equalSampleReserve_card_le R x j ω
    rw [hparams.2.2]
    linarith
  exact equal_variance_from_counts P (by exact_mod_cast hn) ha hp hq hg.1 hg.2.2
    hpop hmark hdraw hcomp

end RiffleUpperV2.Anchor
