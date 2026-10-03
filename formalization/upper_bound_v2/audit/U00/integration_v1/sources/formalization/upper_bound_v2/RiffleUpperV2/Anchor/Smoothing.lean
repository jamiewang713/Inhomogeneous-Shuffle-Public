import RiffleUpperV2.Anchor.SmoothingData

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

/-- Full post-anchor smoothing construction. Every law, good event and
variance estimate is derived from the fixed-count columns. The continuation
may equal its join; no lower bound by one on a side mean is imposed. -/
def endpointSmoothing {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (c₀ : ℤ) (R : Finset (Fin n)) {g χ : ℝ} {y z v x : Prefix k d}
    (hg : Reserve R g) (h : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x) :
    EndpointSmoothingData cuts c₀ R x g (sideScale cuts R v) (varianceDenominator χ v) := by
  have hall := genuine_continuation_maximizers cuts hn R h hvx
  let i := Classical.choose hall.2.2
  let j := Classical.choose (Classical.choose_spec hall.2.2)
  have he := Classical.choose_spec (Classical.choose_spec hall.2.2)
  change leftMean cuts R x i = leftScale cuts R v ∧ rightMean cuts R x j = rightScale cuts R v at he
  have hD₁ := varianceDenominator_gt_one v h.chi_pos h.chi_lt_one
  have hD : 0 < varianceDenominator χ v := lt_trans (by norm_num) hD₁
  have hw : 0 < sideScale cuts R v := lt_min hall.1 hall.2.1
  have hM : (0 : ℝ) < R.card := by
    have hR : R.card ≠ 0 := by
      intro hz
      have hl := h.legal_join
      simp only [Legal, anchoredMean, hz, Nat.cast_zero, zero_mul, lt_self_iff_false] at hl
    exact_mod_cast Nat.pos_of_ne_zero hR
  have hbound := anchoredMass_le_sideMaximum cuts hn R h
  have hweak : g*sideScale cuts R v/(16*varianceDenominator χ v) ≤
      g*sideScale cuts R v/(8*varianceDenominator χ v) :=
    div_le_div_of_nonneg_left (mul_nonneg hg.1.le hw.le) (by positivity) (by nlinarith)
  have hside := varianceSideMinimum hall.1 hall.2.1 hM hD hg.1.le hbound
  by_cases hij : i.val < j.val
  · refine { toEndpointReveal := exactUnequalReveal cuts .upper c₀ R x j i
             failure := ?_, variance := ?_ }
    · have hf := smoothingFailure_unequal cuts hn .upper R x j i hij hg
      change probability (fixedCountPMF cuts) (fun ω => ¬ unequalGood cuts .upper R x j i ω) ≤ _
      simpa only [sideMean, oppositeMean, he.1, he.2, sideScale, min_comm] using hf
    · intro ω hgood
      have hp := endpointVariance_unequal_product cuts hn .upper R x j i hij hg
        (by simpa only [sideMean, he.2] using hall.2.1) ω hgood
      have hp' : g*leftScale cuts R v*rightScale cuts R v/(8*(R.card : ℝ)) ≤
          (unequalEndpointParams .upper R x i ω).varianceFormula := by
        have hh : sideMean .upper cuts R x j = rightScale cuts R v := he.2
        have hh' : oppositeMean .upper cuts R x i = leftScale cuts R v := he.1
        rw [hh,hh'] at hp
        calc
          _ = g*rightScale cuts R v*leftScale cuts R v/(8*(R.card : ℝ)) := by ring
          _ ≤ _ := hp
      exact hweak.trans (hside.trans hp')
  · by_cases heq : i = j
    · have hej : rightMean cuts R x i = rightScale cuts R v := by rw [heq]; exact he.2
      refine { toEndpointReveal := exactEqualReveal cuts c₀ R x i
               failure := ?_, variance := ?_ }
      · change probability (fixedCountPMF cuts) (fun ω => ¬ equalGood cuts R x i ω) ≤ _
        have hf := smoothingFailure_equal cuts hn R x i hg
        rw [he.1] at hf
        have hc := RiffleLowerV2.Thinning.chernoffConstant_pos.le
        have hs : sideScale cuts R v ≤ leftScale cuts R v := min_le_left _ _
        have hex := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr (mul_nonneg hc hg.1.le)))
        have hpos := Real.exp_pos (-RiffleLowerV2.chernoffConstant*g*sideScale cuts R v)
        simp only [neg_mul] at hex hf hpos ⊢
        linarith
      · intro ω hgood
        have hp := endpointVariance_equal cuts hn R x i hg
          (by rw [he.1]; exact hall.1) (by rw [hej]; exact hall.2.1) ω hgood
        rw [he.1,hej] at hp
        have hw' : g*sideScale cuts R v/(16*varianceDenominator χ v) ≤ g*sideScale cuts R v/8 :=
          div_le_div_of_nonneg_left (mul_nonneg hg.1.le hw.le) (by norm_num) (by nlinarith)
        exact hw'.trans hp
    · have hji : j.val < i.val := by
        have hne : i.val ≠ j.val := fun hh => heq (Fin.ext hh)
        omega
      refine { toEndpointReveal := exactUnequalReveal cuts .lower c₀ R x i j
               failure := ?_, variance := ?_ }
      · have hf := smoothingFailure_unequal cuts hn .lower R x i j hji hg
        change probability (fixedCountPMF cuts) (fun ω => ¬ unequalGood cuts .lower R x i j ω) ≤ _
        simpa only [sideMean, oppositeMean, he.1, he.2, sideScale] using hf
      · intro ω hgood
        have hp := endpointVariance_unequal_product cuts hn .lower R x i j hji hg
          (by simpa only [sideMean, he.1] using hall.1) ω hgood
        have hh : sideMean .lower cuts R x i = leftScale cuts R v := he.1
        have hh' : oppositeMean .lower cuts R x j = rightScale cuts R v := he.2
        rw [hh,hh'] at hp
        exact hweak.trans (hside.trans hp)

/-- Public exact shifted law, with the reveal chosen by the proved constructor. -/
theorem endpointShiftHypergeometric {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (c₀ : ℤ) (R : Finset (Fin n)) {g χ : ℝ} {y z v x : Prefix k d}
    (hg : Reserve R g) (h : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x)
    (ω₀ : Sample cuts) (f : ℤ → ℝ) :
    let data := endpointSmoothing cuts hn c₀ R hg h hvx
    conditionalExpect (fixedCountPMF cuts) (fun ω => f (lowerEndpoint c₀ R x ω))
      (fun ω => data.history ω = data.history ω₀) =
        expect (data.params ω₀).law.toPMF (fun q => f (data.shift ω₀ + q.val)) ∧
    conditionalExpect (fixedCountPMF cuts) (fun ω => f (upperEndpoint c₀ R x ω))
      (fun ω => data.history ω = data.history ω₀) =
        expect (data.params ω₀).law.toPMF (fun q => f (data.shift ω₀ + q.val + (prefixRows R x ω₀).card)) :=
  (endpointSmoothing cuts hn c₀ R hg h hvx).endpoint_law ω₀ f

theorem smoothingFailure {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (c₀ : ℤ) (R : Finset (Fin n)) {g χ : ℝ} {y z v x : Prefix k d}
    (hg : Reserve R g) (h : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x) :
    probability (fixedCountPMF cuts) (fun ω => ¬ (endpointSmoothing cuts hn c₀ R hg h hvx).good ω) ≤
      3 * Real.exp (-RiffleLowerV2.chernoffConstant*g*sideScale cuts R v) :=
  (endpointSmoothing cuts hn c₀ R hg h hvx).failure

theorem endpointVariance {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (c₀ : ℤ) (R : Finset (Fin n)) {g χ : ℝ} {y z v x : Prefix k d}
    (hg : Reserve R g) (h : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x)
    (ω : Sample cuts) (hs : (endpointSmoothing cuts hn c₀ R hg h hvx).good ω) :
    g*sideScale cuts R v/(16*varianceDenominator χ v) ≤
      ((endpointSmoothing cuts hn c₀ R hg h hvx).params ω).varianceFormula :=
  (endpointSmoothing cuts hn c₀ R hg h hvx).variance ω hs

end RiffleUpperV2.Anchor
