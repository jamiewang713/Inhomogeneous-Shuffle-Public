import RiffleUpperV2.Shared.Infimum
import RiffleUpperV2.Margins.Suffix

/-! Finite empirical numerical estimates. The scalar class hypotheses here are
explicit intermediate obligations; this module does not assert the model F. -/
noncomputable section
open Set
open scoped BigOperators
namespace RiffleUpperV2.FirstMoment
open TimeProfile

/-- The exact large-class loss in eq:ub-empirical-large-exponent. -/
theorem largeExponent_core {ell V F E H S Q beta B D theta delta q eH : ℝ}
    (htheta : theta ∈ Icc (3 : ℝ) 4) (hdelta : 0 ≤ delta) (hq : 0 ≤ q)
    (hmass : ell = V-S-Q) (hQ : 0 ≤ Q) (hstable : ell-F ≤ delta)
    (hfluc : V-q ≤ 2*F) (hmax : V ≤ beta)
    (hentropy : H ≤ theta*S-B+eH) (htail : E = -D) :
    H+4*ell-F+2*E ≤ (theta+3)/2*beta-B-2*D+delta+q/2+eH := by
  have hm := mul_le_mul_of_nonneg_left (le_of_eq hmass)
    (show 0 ≤ theta by linarith [htheta.1])
  have hq' := mul_nonneg (show 0 ≤ theta by linarith [htheta.1]) hQ
  have hs := mul_le_mul_of_nonneg_left hstable
    (show 0 ≤ 4-theta by linarith [htheta.2])
  have hf := mul_le_mul_of_nonneg_left hfluc
    (show 0 ≤ theta-3 by linarith [htheta.1])
  have hb := mul_le_mul_of_nonneg_left hmax
    (show 0 ≤ (theta+3)/2 by linarith [htheta.1])
  have hd := mul_nonneg (show 0 ≤ theta-3 by linarith [htheta.1]) hdelta
  have hq'' := mul_nonneg (show 0 ≤ 4-theta by linarith [htheta.2]) hq
  nlinarith

/-- Repaired small-proper argument; no smallObjective or second margin is used. -/
theorem smallExponent_core {ell V F E H S beta B D theta delta q eH : ℝ}
    (htheta : theta ∈ Icc (3 : ℝ) 4) (hq : 0 ≤ q)
    (hS : 0 ≤ S) (hparent : S ≤ V-F+q) (hfluc : V-q ≤ 2*F)
    (hmax : V ≤ beta) (hsmall : ell ≤ 2*delta)
    (hentropy : H ≤ theta*S-B+eH) (htail : E = -D) :
    H+4*ell+2*E ≤ (theta+3)/2*beta-B-2*D+8*delta+21*q/2+eH := by
  have hbound : S ≤ beta/2+3*q/2 := by linarith
  have hm := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ theta+3 by linarith [htheta.1])
  have he := mul_nonneg (show 0 ≤ 4-theta by linarith [htheta.2]) hq
  nlinarith

/-- Empirical large exponent at integer endpoints, using the proved attained infimum. -/
theorem empiricalLargeExponent {k n L N a s u : ℕ} (cuts : Cuts k n L)
    (hn : 0 < n) {eta ell V F E H S Q delta q eH : ℝ}
    (hmargin : EmpiricalNegativeMargin N a cuts hn eta)
    (has : a ≤ s) (hsu : s ≤ u) (hu : u ≤ a+L)
    (hdelta : 0 ≤ delta) (hq : 0 ≤ q)
    (hmass : ell = V-S-Q) (hQ : 0 ≤ Q) (hstable : ell-F ≤ delta)
    (hfluc : V-q ≤ 2*F) (hmax : V ≤ empiricalBeta N a cuts hn s)
    (hentropy : ∀ theta ∈ Icc (3 : ℝ) 4,
      H ≤ theta*S-empiricalB N a cuts hn theta s u+eH)
    (htail : E = -empiricalB N a cuts hn 2 u (a+L)) :
    H+4*ell-F+2*E ≤ -eta+delta+q/2+eH := by
  obtain ⟨theta, htheta, heq⟩ := empiricalInf_attained N a cuts hn s u
  have h := largeExponent_core htheta hdelta hq hmass hQ hstable hfluc hmax
    (hentropy theta htheta) htail
  change H+4*ell-F+2*E ≤ empiricalExpression N a cuts hn theta s u+delta+q/2+eH at h
  rw [heq] at h
  linarith [hmargin.2 s u has hsu hu]

/-- Empirical small-proper exponent, preserving the source's fixed error. -/
theorem empiricalSmallExponent {k n L N a s u : ℕ} (cuts : Cuts k n L)
    (hn : 0 < n) {eta ell V F E H S delta q eH : ℝ}
    (hmargin : EmpiricalNegativeMargin N a cuts hn eta)
    (has : a ≤ s) (hsu : s ≤ u) (hu : u ≤ a+L)
    (hq : 0 ≤ q) (hS : 0 ≤ S) (hparent : S ≤ V-F+q)
    (hfluc : V-q ≤ 2*F) (hmax : V ≤ empiricalBeta N a cuts hn s)
    (hsmall : ell ≤ 2*delta)
    (hentropy : ∀ theta ∈ Icc (3 : ℝ) 4,
      H ≤ theta*S-empiricalB N a cuts hn theta s u+eH)
    (htail : E = -empiricalB N a cuts hn 2 u (a+L)) :
    H+4*ell+2*E ≤ -eta+8*delta+21*q/2+eH := by
  obtain ⟨theta, htheta, heq⟩ := empiricalInf_attained N a cuts hn s u
  have h := smallExponent_core htheta hq hS hparent hfluc hmax hsmall
    (hentropy theta htheta) htail
  change H+4*ell+2*E ≤ empiricalExpression N a cuts hn theta s u+8*delta+21*q/2+eH at h
  rw [heq] at h
  linarith [hmargin.2 s u has hsu hu]

/-- Collision cost dominates maximum-digit cost even with zero piles. -/
theorem maxCost_le_psi_two {k : ℕ} (p : Simplex k) : maxCost p ≤ psi p 2 := by
  have hsum : powerSum p 2 ≤ pileMax p := by
    calc
      powerSum p 2 = ∑ l, prob p l * prob p l := by
        simp only [powerSum, Real.rpow_two, pow_two]
      _ ≤ ∑ l, prob p l * pileMax p := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left (prob_le_pileMax p l) (prob_nonneg p l)
      _ = pileMax p := by rw [← Finset.sum_mul, sum_prob, one_mul]
  have h := Real.log_le_log (powerSum_pos p (by norm_num : (1 : ℝ) ≤ 2)) hsum
  simp only [maxCost, digitCost, one_div, Real.log_inv, psi]
  linarith

/-- The cumulative comparison uses original log N, including subdecks. -/
theorem empiricalA_le_B_two {k n L N : ℕ} (hN : 2 ≤ N) (a : ℕ)
    (cuts : Cuts k n L) (hn : 0 < n) (s u : ℕ) :
    empiricalA N a cuts hn s u ≤ empiricalB N a cuts hn 2 s u := by
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun j _ => maxCost_le_psi_two (cuts.profile hn j)
  · exact (logScale_pos hN).le

/-- Immediate-stop singletons need only the terminal empirical margin. -/
theorem empiricalImmediateExponent {k n L N : ℕ} (hN : 2 ≤ N) (a : ℕ)
    (cuts : Cuts k n L) (hn : 0 < n) {s : ℕ} {eta ell E : ℝ}
    (has : a ≤ s) (hs : s ≤ a+L)
    (hterminal : empiricalBeta N a cuts hn (a+L) ≤ -eta)
    (hmax : ell ≤ empiricalBeta N a cuts hn s)
    (htail : E = -empiricalB N a cuts hn 2 s (a+L)) : ell+E ≤ -eta := by
  have hAB := empiricalA_le_B_two hN a cuts hn s (a+L)
  have hsplit := Margins.empiricalA_add hN a cuts hn has hs
  unfold empiricalBeta at hmax hterminal
  linarith

/-- The subsequent density exponent for a small immediate singleton. -/
theorem immediateSmallDensityExponent {ell E eta delta : ℝ}
    (hmargin : ell+E ≤ -eta) (hsmall : ell ≤ 2*delta) :
    4*ell+2*E ≤ -2*eta+4*delta := by linarith

end RiffleUpperV2.FirstMoment
