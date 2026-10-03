import RiffleUpperV2.Anchor.Smoothing

noncomputable section
set_option maxHeartbeats 500000
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric RiffleLowerV2.Thinning.Compat

theorem conditionalProbability_indicator {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (E F : Ω → Prop) :
    conditionalProbability P E F = conditionalExpect P (fun ω => if E ω then 1 else 0) F := by
  unfold conditionalProbability conditionalExpect RiffleLowerV2.conditionalProbability
    RiffleLowerV2.conditionalExpect RiffleLowerV2.probability RiffleLowerV2.expect
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : E ω <;> by_cases hf : F ω <;> simp [he,hf]

/-- Integer shifts include negative endpoint offsets; unsupported integer
atoms have zero mass and all supported atoms reduce to the U02 natural atom. -/
theorem shiftedHypergeomAtom (P : HypergeomParams) (hv : 0 < P.varianceFormula) (a b z : ℤ) :
    probability P.law.toPMF (fun q => a + q.val + b = z) ≤ 4 / Real.sqrt P.varianceFormula := by
  by_cases h : ∃ q : Fin (P.draws+1), a + q.val + b = z
  · obtain ⟨q₀,hq₀⟩ := h
    have he : (fun q : Fin (P.draws+1) => a + q.val + b = z) = (fun q => q.val = q₀.val) := by
      funext q
      apply propext
      omega
    rw [he]
    exact atomBound P hv q₀.val
  · have hh : ∀ q : Fin (P.draws+1), ¬ (a + q.val + b = z) := not_exists.mp h
    have hz : probability P.law.toPMF (fun q => a + q.val + b = z) = 0 := by
      simp only [probability, RiffleLowerV2.probability, RiffleLowerV2.expect,
        hh, if_false, mul_zero, Finset.sum_const_zero]
    rw [hz]
    positivity

/-- Both endpoint atoms on a realized fine fiber follow from the exact
shifted law. The good-event variance input is supplied by endpointSmoothing. -/
theorem EndpointReveal.fine_atoms {k n d : ℕ} {cuts : Cuts k n d} {c₀ : ℤ}
    {R : Finset (Fin n)} {x : Prefix k d} (data : EndpointReveal cuts c₀ R x)
    (ω₀ : Sample cuts) (hv : 0 < (data.params ω₀).varianceFormula) (z : ℤ) :
    conditionalProbability (fixedCountPMF cuts) (fun ω => lowerEndpoint c₀ R x ω = z)
      (fun ω => data.history ω = data.history ω₀) ≤ 4 / Real.sqrt (data.params ω₀).varianceFormula ∧
    conditionalProbability (fixedCountPMF cuts) (fun ω => upperEndpoint c₀ R x ω = z)
      (fun ω => data.history ω = data.history ω₀) ≤ 4 / Real.sqrt (data.params ω₀).varianceFormula := by
  have he := data.endpoint_law ω₀ (fun r => if r = z then 1 else 0)
  constructor
  · calc
      _ = conditionalExpect (fixedCountPMF cuts)
          (fun ω => if lowerEndpoint c₀ R x ω = z then 1 else 0)
          (fun ω => data.history ω = data.history ω₀) := by
        unfold conditionalProbability conditionalExpect RiffleLowerV2.conditionalProbability
          RiffleLowerV2.conditionalExpect RiffleLowerV2.probability RiffleLowerV2.expect
        congr 1
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hE : lowerEndpoint c₀ R x ω = z <;>
          by_cases hF : data.history ω = data.history ω₀ <;> simp [hE,hF]
      _ = expect (data.params ω₀).law.toPMF (fun q => if data.shift ω₀ + q.val = z then 1 else 0) := he.1
      _ = probability (data.params ω₀).law.toPMF (fun q => data.shift ω₀ + q.val = z) := by
        unfold expect probability RiffleLowerV2.probability RiffleLowerV2.expect
        apply Finset.sum_congr rfl
        intro q _
        dsimp only
        split_ifs <;> rfl
      _ ≤ _ := by simpa only [add_zero] using shiftedHypergeomAtom (data.params ω₀) hv (data.shift ω₀) 0 z
  · calc
      _ = conditionalExpect (fixedCountPMF cuts)
          (fun ω => if upperEndpoint c₀ R x ω = z then 1 else 0)
          (fun ω => data.history ω = data.history ω₀) := by
        unfold conditionalProbability conditionalExpect RiffleLowerV2.conditionalProbability
          RiffleLowerV2.conditionalExpect RiffleLowerV2.probability RiffleLowerV2.expect
        congr 1
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hE : upperEndpoint c₀ R x ω = z <;>
          by_cases hF : data.history ω = data.history ω₀ <;> simp [hE,hF]
      _ = expect (data.params ω₀).law.toPMF
          (fun q => if data.shift ω₀ + q.val + (prefixRows R x ω₀).card = z then 1 else 0) := he.2
      _ = probability (data.params ω₀).law.toPMF
          (fun q => data.shift ω₀ + q.val + (prefixRows R x ω₀).card = z) := by
        unfold expect probability RiffleLowerV2.probability RiffleLowerV2.expect
        apply Finset.sum_congr rfl
        intro q _
        dsimp only
        split_ifs <;> rfl
      _ ≤ _ := shiftedHypergeomAtom (data.params ω₀) hv (data.shift ω₀) (prefixRows R x ω₀).card z

end RiffleUpperV2.Anchor
