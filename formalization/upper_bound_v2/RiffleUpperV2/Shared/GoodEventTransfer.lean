import RiffleUpperV2.Shared.FiniteAveraging
import RiffleLowerV2.Thinning.PMFTools

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2
open RiffleLowerV2.Thinning

/-- Average an event bound valid on good fine fibers to any positive coarse
fiber. The good event stays inside the event whose probability is bounded. -/
theorem conditionalGoodEvent_le_of_refinement {Ω Γ Δ : Type*}
    [Fintype Ω] [Fintype Γ] [Fintype Δ] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ)
    (href : ∀ ω ω', Z ω = Z ω' → U ω = U ω')
    (E S : Ω → Prop)
    (hS : ∀ ω ω', Z ω = Z ω' → (S ω ↔ S ω'))
    (b : ℝ) (hb : 0 ≤ b)
    (hpoint : ∀ ω, 0 < probability P (fun v => Z v = Z ω) → S ω →
      conditionalProbability P E (fun v => Z v = Z ω) ≤ b)
    (u : Δ) (hu : 0 < probability P (fun ω => U ω = u)) :
    conditionalProbability P (fun ω => E ω ∧ S ω) (fun ω => U ω = u) ≤ b := by
  obtain ⟨g,hg⟩ := history_refinement_factors Z U u href
  apply conditionalProbability_le_of_refinement P Z U g hg _ b _ u hu
  intro z hz
  obtain ⟨ω₀,hz₀⟩ := probability_pos_exists P (fun ω => Z ω = z) hz
  by_cases hs : S ω₀
  · have hp := hpoint ω₀ (by simpa only [hz₀] using hz) hs
    rw [hz₀] at hp
    apply le_trans _ hp
    unfold conditionalProbability RiffleLowerV2.conditionalProbability
    apply div_le_div_of_nonneg_right _ hz.le
    exact probability_mono P (fun _ h => ⟨h.1.1,h.2⟩)
  · have he : (fun ω => (E ω ∧ S ω) ∧ Z ω = z) = (fun _ => False) := by
      funext ω
      apply propext
      constructor
      · intro h
        exact hs ((hS ω ω₀ (h.2.trans hz₀.symm)).mp h.1.2)
      · exact False.elim
    unfold conditionalProbability RiffleLowerV2.conditionalProbability
    rw [he]
    simpa only [probability, RiffleLowerV2.probability, RiffleLowerV2.expect,
      if_false, mul_zero, Finset.sum_const_zero, zero_div] using hb

end RiffleUpperV2
