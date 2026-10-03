import RiffleUpperV2.Anchor.UnequalSideBounds

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric

theorem sideMean_nonneg {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val) : 0 ≤ sideMean s cuts R x i := by
  cases s
  · exact leftMean_nonneg cuts R x i
  · exact rightMean_nonneg cuts R x i

theorem oppositeMean_nonneg {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val) : 0 ≤ oppositeMean s cuts R x i := by
  cases s
  · exact rightMean_nonneg cuts R x i
  · exact leftMean_nonneg cuts R x i

/-- The exact source failure constant, symmetrically in the two side masses. -/
theorem smoothingFailure_unequal {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    (hji : j.val < i.val) {g : ℝ} (hg : Reserve R g) :
    probability (fixedCountPMF cuts) (fun ω => ¬ unequalGood cuts s R x i j ω) ≤
      3 * Real.exp (-RiffleLowerV2.chernoffConstant * g *
        min (sideMean s cuts R x i) (oppositeMean s cuts R x j)) := by
  let m := min (sideMean s cuts R x i) (oppositeMean s cuts R x j)
  have hm₀ : 0 ≤ m := le_min (sideMean_nonneg cuts s R x i) (oppositeMean_nonneg cuts s R x j)
  have hm : g*m ≤ witnessMean cuts s R x i j := by
    have hs := (min_le_left (sideMean s cuts R x i) (oppositeMean s cuts R x j)).trans
      (witnessMean_ge_sideMean cuts hn s R x i j hji)
    change m ≤ _ at hs
    nlinarith [hg.2.1]
  have hcounts := unequal_side_count_bounds cuts hn s R x i j hji
  have hD : m ≤ allowedCount cuts (prefixColumn x j) (s.allowed (x.2.get j)) ∧
      m ≤ allowedCount cuts (prefixColumn x j) (Finset.univ \ s.allowed (x.2.get j)) := by
    have hl := (min_le_left (sideMean s cuts R x i) (oppositeMean s cuts R x j)).trans hcounts.1
    have hr := (min_le_right (sideMean s cuts R x i) (oppositeMean s cuts R x j)).trans hcounts.2
    cases s
    · rw [(unequal_digitSets (x.2.get j)).2.1, (unequal_digitSets (x.2.get j)).1]
      exact ⟨hl,hr⟩
    · rw [(unequal_digitSets (x.2.get j)).2.2.2, (unequal_digitSets (x.2.get j)).2.2.1]
      exact ⟨hr,hl⟩
  have hc := RiffleLowerV2.Thinning.chernoffConstant_pos.le
  have h₀ := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr hc))
  have h₁ := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
    (mul_le_mul_of_nonneg_left hD.1 hg.1.le) (neg_nonpos.mpr hc))
  have h₂ := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
    (mul_le_mul_of_nonneg_left hD.2 hg.1.le) (neg_nonpos.mpr hc))
  apply (unequalGood_failure_raw cuts hn s R x i j hg).trans
  simp only [← mul_assoc] at h₀ h₁ h₂
  change _ ≤ 3 * Real.exp (-RiffleLowerV2.chernoffConstant * g * m)
  linarith

/-- Both unequal cases have the same symmetric product variance lower bound,
derived from the actual witness and residual counts on unequalGood. -/
theorem endpointVariance_unequal_product {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    (hji : j.val < i.val) {g : ℝ} (hg : Reserve R g)
    (hs : 0 < sideMean s cuts R x i) (ω : Sample cuts) (hgood : unequalGood cuts s R x i j ω) :
    g * sideMean s cuts R x i * oppositeMean s cuts R x j / (8*(R.card : ℝ)) ≤
      (unequalEndpointParams s R x j ω).varianceFormula := by
  have hw : 0 < witnessMean cuts s R x i j := hs.trans_le (witnessMean_ge_sideMean cuts hn s R x i j hji)
  have hM : (0 : ℝ) < R.card := hw.trans_le (witnessMean_le_card cuts s R x i j)
  have hv := unequalVariance_good_counts cuts hn s R x i j hji hg hw ω hgood
  have hprod := witnessVarianceProduct hw.le
    (by unfold digitProbability; positivity : 0 ≤ digitProbability cuts (prefixColumn x j) (x.2.get j))
    (by positivity : 0 ≤ (allowedCount cuts (prefixColumn x j) (s.containingDigits (x.2.get j)) : ℝ)/n)
    (by positivity : 0 ≤ (allowedCount cuts (prefixColumn x j) (s.oppositeDigits (x.2.get j)) : ℝ)/n)
    (oppositeMean_nonneg cuts s R x j) hM hg.1.le
    (witnessMean_mul_digit cuts hn s R x i j hji) (containing_digitProbability cuts s _ _)
    (oppositeMean_div_card cuts hn s R (by exact_mod_cast hM) x j)
  apply hprod.trans
  cases s
  · rw [(unequal_digitSets (x.2.get j)).2.1, (unequal_digitSets (x.2.get j)).1] at hv
    exact hv
  · have hv' := hv
    rw [(unequal_digitSets (x.2.get j)).2.2.2, (unequal_digitSets (x.2.get j)).2.2.1] at hv'
    nlinarith [hv']

end RiffleUpperV2.Anchor
