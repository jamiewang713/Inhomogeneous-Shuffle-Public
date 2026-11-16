import RiffleUpperV2.Shared.FiniteAveraging

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2
open RiffleLowerV2.Thinning.Compat

/-- Restrict a uniform conditional bound to an arbitrary event in the
conditioning history. Null history atoms retain zero weight. -/
theorem joint_historyEvent_bound {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : PMF Ω) (U : Ω → Γ) (E : Ω → Prop) (H : Γ → Prop) (b : ℝ)
    (hpoint : ∀ u, 0 < probability P (fun ω => U ω = u) → H u →
      conditionalProbability P E (fun ω => U ω = u) ≤ b) :
    probability P (fun ω => E ω ∧ H (U ω)) ≤
      b * probability P (fun ω => H (U ω)) := by
  let p := toCompatFiniteLaw P
  have hp : ∀ u, 0 < p.prob (fun ω => U ω = u) →
      p.conditionalProb (fun ω => U ω = u) (fun ω => E ω ∧ H (U ω)) ≤
        if H u then b else 0 := by
    intro u hu
    by_cases hH : H u
    · rw [if_pos hH]
      apply (p.conditionalProb_mono_on _ _ E (fun _ _ h => h.1)).trans
      simpa only [p, toCompatFiniteLaw_conditionalProbability] using
        hpoint u (by simpa only [p, toCompatFiniteLaw_probability] using hu) hH
    · rw [if_neg hH]
      apply (p.conditionalProb_mono_on _ _ (fun _ => False) ?_).trans
      · simp [FiniteLaw.conditionalProb, FiniteLaw.prob]
      · intro ω hω h
        exact hH (hω ▸ h.2)
  have h := p.total_probability_bound U (fun ω => E ω ∧ H (U ω))
    (fun u => if H u then b else 0) hp
  have he : (∑ u, p.prob (fun ω => U ω = u) * (if H u then b else 0)) =
      b * p.prob (fun ω => H (U ω)) := by
    calc
      _ = (∑ u, if H u then p.prob (fun ω => U ω = u) else 0) * b := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : H u <;> simp [hu]
      _ = (p.map U).prob H * b := rfl
      _ = _ := by rw [FiniteLaw.map_prob, mul_comm]
  rw [he] at h
  simpa only [p, toCompatFiniteLaw_probability] using h

end RiffleUpperV2
