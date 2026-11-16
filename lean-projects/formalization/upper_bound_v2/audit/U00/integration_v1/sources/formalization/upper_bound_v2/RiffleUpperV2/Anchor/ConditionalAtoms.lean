import RiffleUpperV2.Anchor.FineAtoms
import RiffleUpperV2.Shared.GoodEventTransfer

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

theorem smoothingAtomConstant {g w D : ℝ} (hg : 0 < g) (hw : 0 < w) (hD : 0 < D) :
    4 / Real.sqrt (g*w/(16*D)) = 16 * Real.sqrt (D/(g*w)) := by
  rw [Real.sqrt_div (mul_nonneg hg.le hw.le), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
    Real.sqrt_div hD.le]
  norm_num
  field_simp
  <;> norm_num

/-- Coarse endpoint atoms retain the smoothing indicator inside the event.
This generic projection is applied below only to constructed smoothing data. -/
theorem EndpointSmoothingData.coarse_atoms {k n d : ℕ} {cuts : Cuts k n d} {c₀ : ℤ}
    {R : Finset (Fin n)} {x : Prefix k d} {g w D : ℝ}
    (data : EndpointSmoothingData cuts c₀ R x g w D)
    (hg : 0 < g) (hw : 0 < w) (hD : 0 < D)
    (u : InternalHistory k n d)
    (hu : 0 < probability (fixedCountPMF cuts) (fun ω => internalHistory R x ω = u)) (z : ℤ) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => lowerEndpoint c₀ R x ω = z ∧ data.good ω)
      (fun ω => internalHistory R x ω = u) ≤ 16*Real.sqrt (D/(g*w)) ∧
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => upperEndpoint c₀ R x ω = z ∧ data.good ω)
      (fun ω => internalHistory R x ω = u) ≤ 16*Real.sqrt (D/(g*w)) := by
  letI : Fintype data.History := data.finiteHistory
  have hc : 0 < g*w/(16*D) := by positivity
  have hp (ω₀ : Sample cuts) (hs : data.good ω₀) :
      conditionalProbability (fixedCountPMF cuts) (fun ω => lowerEndpoint c₀ R x ω = z)
        (fun ω => data.history ω = data.history ω₀) ≤ 16*Real.sqrt (D/(g*w)) ∧
      conditionalProbability (fixedCountPMF cuts) (fun ω => upperEndpoint c₀ R x ω = z)
        (fun ω => data.history ω = data.history ω₀) ≤ 16*Real.sqrt (D/(g*w)) := by
    have hv := data.variance ω₀ hs
    have hh := data.toEndpointReveal.fine_atoms ω₀ (hc.trans_le hv) z
    have hb : 4/Real.sqrt (data.params ω₀).varianceFormula ≤ 16*Real.sqrt (D/(g*w)) := by
      rw [← smoothingAtomConstant hg hw hD]
      exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hc) (Real.sqrt_le_sqrt hv)
    exact ⟨hh.1.trans hb,hh.2.trans hb⟩
  constructor
  · exact conditionalGoodEvent_le_of_refinement (fixedCountPMF cuts) data.history (internalHistory R x)
      data.refines (fun ω => lowerEndpoint c₀ R x ω = z) data.good
      (fun ω ω' he => data.good_measurable ω' ω he) _ (by positivity)
      (fun ω₀ _ hs => (hp ω₀ hs).1) u hu
  · exact conditionalGoodEvent_le_of_refinement (fixedCountPMF cuts) data.history (internalHistory R x)
      data.refines (fun ω => upperEndpoint c₀ R x ω = z) data.good
      (fun ω ω' he => data.good_measurable ω' ω he) _ (by positivity)
      (fun ω₀ _ hs => (hp ω₀ hs).2) u hu

/-- The source anchored endpoint anti-concentration theorem on every positive
internal-history atom, for both endpoints and every integer rank. The source
constant C_hyp is 4 here, so the displayed constant is 4*C_hyp=16. -/
theorem conditionalEndpointAtoms {k n d : ℕ} (cuts : Cuts k n d) (hn : 2 ≤ n) (_hd : 1 ≤ d)
    (c₀ : ℤ) (R : Finset (Fin n)) {g χ : ℝ} {y z v x : Prefix k d}
    (hg : Reserve R g) (h : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x)
    (u : InternalHistory k n d)
    (hu : 0 < probability (fixedCountPMF cuts) (fun ω => internalHistory R x ω = u)) (rank : ℤ) :
    let data := endpointSmoothing cuts (by omega) c₀ R hg h hvx
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => lowerEndpoint c₀ R x ω = rank ∧ data.good ω)
      (fun ω => internalHistory R x ω = u) ≤
        16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v)) ∧
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => upperEndpoint c₀ R x ω = rank ∧ data.good ω)
      (fun ω => internalHistory R x ω = u) ≤
        16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v)) := by
  have hs := genuine_sideScale_pos cuts (by omega) R h
  exact (endpointSmoothing cuts (by omega) c₀ R hg h hvx).coarse_atoms hg.1
    (hs.1.trans_le hs.2) (lt_trans (by norm_num) (varianceDenominator_gt_one v h.chi_pos h.chi_lt_one))
    u hu rank

end RiffleUpperV2.Anchor
