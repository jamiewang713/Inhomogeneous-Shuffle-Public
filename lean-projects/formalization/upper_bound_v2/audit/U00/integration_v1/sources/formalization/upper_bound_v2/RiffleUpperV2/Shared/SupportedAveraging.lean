import RiffleUpperV2.Shared.GoodEventTransfer

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2
open RiffleLowerV2.Thinning.Compat

/-- A supported bound averages with the conditional probability of its support,
rather than replacing that probability by one. -/
theorem conditionalProbability_le_mul_of_refinement {Ω Γ Δ : Type*}
    [Fintype Ω] [Fintype Γ] [Fintype Δ] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ)
    (href : ∀ ω ω', Z ω = Z ω' → U ω = U ω')
    (E B : Ω → Prop) (b : ℝ)
    (hpoint : ∀ z, 0 < probability P (fun ω => Z ω = z) →
      conditionalProbability P E (fun ω => Z ω = z) ≤
        b * conditionalProbability P B (fun ω => Z ω = z))
    (u : Δ) (hu : 0 < probability P (fun ω => U ω = u)) :
    conditionalProbability P E (fun ω => U ω = u) ≤
      b * conditionalProbability P B (fun ω => U ω = u) := by
  obtain ⟨g,hg⟩ := history_refinement_factors Z U u href
  have hu' : 0 < (toCompatFiniteLaw P).prob (fun ω => U ω = u) := by
    simpa only [toCompatFiniteLaw_probability] using hu
  have hp := FiniteLaw.coarse_total_probability_bound (toCompatFiniteLaw P)
    Z U g hg u hu' E
    (fun z => b * (toCompatFiniteLaw P).conditionalProb (fun ω => Z ω = z) B)
    (by simpa only [toCompatFiniteLaw_probability,
      toCompatFiniteLaw_conditionalProbability] using hpoint)
  have ht := FiniteLaw.coarse_total_probability (toCompatFiniteLaw P) Z U g hg u hu' B
  have hresult : (toCompatFiniteLaw P).conditionalProb (fun ω => U ω = u) E ≤
      b * (toCompatFiniteLaw P).conditionalProb (fun ω => U ω = u) B := by
    simpa only [ht,Finset.mul_sum,mul_left_comm] using hp
  simpa only [toCompatFiniteLaw_conditionalProbability] using hresult

/-- Keep a fine-measurable good event inside the target event and retain the
exact fine-measurable support weight on every positive coarse history. -/
theorem conditionalSupportedGoodEvent_le {Ω Γ Δ : Type*}
    [Fintype Ω] [Fintype Γ] [Fintype Δ] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ)
    (href : ∀ ω ω', Z ω = Z ω' → U ω = U ω')
    (E S : Ω → Prop) (B : Γ → Prop)
    (hS : ∀ ω ω', Z ω = Z ω' → (S ω ↔ S ω'))
    (hE : ∀ ω, E ω → B (Z ω)) (b : ℝ) (hb : 0 ≤ b)
    (hpoint : ∀ ω, 0 < probability P (fun v => Z v = Z ω) → S ω → B (Z ω) →
      conditionalProbability P E (fun v => Z v = Z ω) ≤ b)
    (u : Δ) (hu : 0 < probability P (fun ω => U ω = u)) :
    conditionalProbability P (fun ω => E ω ∧ S ω) (fun ω => U ω = u) ≤
      b * conditionalProbability P (fun ω => B (Z ω)) (fun ω => U ω = u) := by
  apply conditionalProbability_le_mul_of_refinement P Z U href _ _ b _ u hu
  intro z hz
  obtain ⟨ω₀,hz₀⟩ := probability_pos_exists P (fun ω => Z ω = z) hz
  have hnonneg : 0 ≤ b * conditionalProbability P (fun ω => B (Z ω))
      (fun ω => Z ω = z) := by
    apply mul_nonneg hb
    simpa only [toCompatFiniteLaw_conditionalProbability] using
      FiniteLaw.conditionalProb_nonneg (toCompatFiniteLaw P)
        (fun ω => Z ω = z) (fun ω => B (Z ω))
  by_cases hs : S ω₀
  · by_cases hB : B z
    · have hsupport : conditionalProbability P (fun ω => B (Z ω))
          (fun ω => Z ω = z) = 1 := by
        have he : (fun ω => B (Z ω) ∧ Z ω = z) = (fun ω => Z ω = z) := by
          funext ω
          exact propext ⟨And.right,fun h => ⟨h ▸ hB,h⟩⟩
        unfold conditionalProbability RiffleLowerV2.conditionalProbability
        rw [he,div_self hz.ne']
      rw [hsupport,mul_one]
      have hp := hpoint ω₀ (by simpa only [hz₀] using hz) hs
        (by simpa only [hz₀] using hB)
      rw [hz₀] at hp
      apply le_trans _ hp
      unfold conditionalProbability RiffleLowerV2.conditionalProbability
      apply div_le_div_of_nonneg_right _ hz.le
      exact RiffleLowerV2.Thinning.probability_mono P (fun _ h => ⟨h.1.1,h.2⟩)
    · have he : (fun ω => (E ω ∧ S ω) ∧ Z ω = z) = (fun _ => False) := by
        funext ω
        apply propext
        exact ⟨fun h => hB (h.2 ▸ hE ω h.1.1),False.elim⟩
      have hzE : conditionalProbability P (fun ω => E ω ∧ S ω)
          (fun ω => Z ω = z) = 0 := by
        unfold conditionalProbability RiffleLowerV2.conditionalProbability
        rw [he]
        simp [RiffleLowerV2.probability,RiffleLowerV2.expect]
      rw [hzE]
      exact hnonneg
  · have he : (fun ω => (E ω ∧ S ω) ∧ Z ω = z) = (fun _ => False) := by
      funext ω
      apply propext
      exact ⟨fun h => hs ((hS ω ω₀ (h.2.trans hz₀.symm)).mp h.1.2),False.elim⟩
    have hzE : conditionalProbability P (fun ω => E ω ∧ S ω)
        (fun ω => Z ω = z) = 0 := by
      unfold conditionalProbability RiffleLowerV2.conditionalProbability
      rw [he]
      simp [RiffleLowerV2.probability,RiffleLowerV2.expect]
    rw [hzE]
    exact hnonneg

end RiffleUpperV2
