import RiffleUpperV2.Anchor.ConditionalAtoms
import RiffleUpperV2.Shared.HistoryEventBound

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

/-- Any offset selected from the complete labeled internal history may be
added before testing the endpoint atom. -/
theorem EndpointSmoothingData.coarse_offset_atoms {k n d : ℕ} {cuts : Cuts k n d} {c₀ : ℤ}
    {R : Finset (Fin n)} {x : Prefix k d} {g w D : ℝ}
    (data : EndpointSmoothingData cuts c₀ R x g w D)
    (hg : 0 < g) (hw : 0 < w) (hD : 0 < D)
    (offset : InternalHistory k n d → ℤ) (rank : ℤ) (u : InternalHistory k n d)
    (hu : 0 < probability (fixedCountPMF cuts) (fun ω => internalHistory R x ω = u)) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => lowerEndpoint c₀ R x ω + offset (internalHistory R x ω) = rank ∧ data.good ω)
      (fun ω => internalHistory R x ω = u) ≤ 16*Real.sqrt (D/(g*w)) ∧
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => upperEndpoint c₀ R x ω + offset (internalHistory R x ω) = rank ∧ data.good ω)
      (fun ω => internalHistory R x ω = u) ≤ 16*Real.sqrt (D/(g*w)) := by
  have hh := data.coarse_atoms hg hw hD u hu (rank-offset u)
  have he (endpoint : Sample cuts → ℤ) :
      conditionalProbability (fixedCountPMF cuts)
        (fun ω => endpoint ω + offset (internalHistory R x ω) = rank ∧ data.good ω)
        (fun ω => internalHistory R x ω = u) =
      conditionalProbability (fixedCountPMF cuts)
        (fun ω => endpoint ω = rank-offset u ∧ data.good ω)
        (fun ω => internalHistory R x ω = u) := by
    apply conditionalProbability_congr_on
    intro ω hf
    rw [hf]
    apply and_congr_left
    intro _
    omega
  exact ⟨(le_of_eq (he (lowerEndpoint c₀ R x))).trans hh.1,
    (le_of_eq (he (upperEndpoint c₀ R x))).trans hh.2⟩

/-- Joint endpoint/internal-continuation estimate: offsets and the internal
event may use the full labeled cylinder and every one of its continuations. -/
theorem jointInternalOffsetAtoms {k n d : ℕ} (cuts : Cuts k n d) (hn : 2 ≤ n) (_hd : 1 ≤ d)
    (c₀ : ℤ) (R : Finset (Fin n)) {g χ : ℝ} {y z v x : Prefix k d}
    (hg : Reserve R g) (h : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x)
    (offset : InternalHistory k n d → ℤ) (H : InternalHistory k n d → Prop) (rank : ℤ) :
    let data := endpointSmoothing cuts (by omega) c₀ R hg h hvx
    probability (fixedCountPMF cuts)
      (fun ω => lowerEndpoint c₀ R x ω + offset (internalHistory R x ω) = rank ∧
        data.good ω ∧ H (internalHistory R x ω)) ≤
      16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v)) *
        probability (fixedCountPMF cuts) (fun ω => H (internalHistory R x ω)) ∧
    probability (fixedCountPMF cuts)
      (fun ω => upperEndpoint c₀ R x ω + offset (internalHistory R x ω) = rank ∧
        data.good ω ∧ H (internalHistory R x ω)) ≤
      16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v)) *
        probability (fixedCountPMF cuts) (fun ω => H (internalHistory R x ω)) := by
  let data := endpointSmoothing cuts (by omega) c₀ R hg h hvx
  have hs := genuine_sideScale_pos cuts (by omega) R h
  have hw : 0 < sideScale cuts R v := hs.1.trans_le hs.2
  have hD : 0 < varianceDenominator χ v := lt_trans (by norm_num)
    (varianceDenominator_gt_one v h.chi_pos h.chi_lt_one)
  constructor
  · have hh := joint_historyEvent_bound (fixedCountPMF cuts) (internalHistory R x)
      (fun ω => lowerEndpoint c₀ R x ω + offset (internalHistory R x ω) = rank ∧ data.good ω)
      H (16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v)))
      (fun u hu _ => (data.coarse_offset_atoms hg.1 hw hD offset rank u hu).1)
    simpa only [and_assoc] using hh
  · have hh := joint_historyEvent_bound (fixedCountPMF cuts) (internalHistory R x)
      (fun ω => upperEndpoint c₀ R x ω + offset (internalHistory R x ω) = rank ∧ data.good ω)
      H (16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v)))
      (fun u hu _ => (data.coarse_offset_atoms hg.1 hw hD offset rank u hu).2)
    simpa only [and_assoc] using hh

end RiffleUpperV2.Anchor
