import RiffleUpperV2.Shared.FiniteLawAdapters

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2
open RiffleLowerV2.Thinning.Compat

/-- Average a bound on every positive history atom. Null atoms have zero
weight, and the event being bounded need not be history measurable. -/
theorem probability_le_of_history {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : PMF Ω) (Z : Ω → Γ) (B : Ω → Prop) (b : ℝ)
    (h : ∀ ω, 0 < probability P (fun v => Z v = Z ω) →
      conditionalProbability P B (fun v => Z v = Z ω) ≤ b) :
    probability P B ≤ b := by
  have hz : ∀ z, 0 < (toCompatFiniteLaw P).prob (fun ω => Z ω = z) →
      (toCompatFiniteLaw P).conditionalProb (fun ω => Z ω = z) B ≤ b := by
    intro z hp
    rw [toCompatFiniteLaw_probability] at hp
    obtain ⟨ω, hω⟩ := probability_pos_exists P _ hp
    simpa only [toCompatFiniteLaw_conditionalProbability, hω] using
      h ω (by simpa only [hω] using hp)
  have hb := FiniteLaw.total_probability_bound (toCompatFiniteLaw P) Z B (fun _ => b) hz
  rw [← Finset.sum_mul, FiniteLaw.sum_atom_prob, one_mul,
    toCompatFiniteLaw_probability] at hb
  exact hb

/-- The same averaging on a positive coarse atom, using the proved old
finite-law tower identity and exactly its conditional weights. -/
theorem conditionalProbability_le_of_refinement {Ω Γ Δ : Type*}
    [Fintype Ω] [Fintype Γ] [Fintype Δ] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ) (g : Γ → Δ) (hU : ∀ ω, U ω = g (Z ω))
    (B : Ω → Prop) (b : ℝ)
    (h : ∀ z, 0 < probability P (fun ω => Z ω = z) →
      conditionalProbability P B (fun ω => Z ω = z) ≤ b)
    (u : Δ) (hu : 0 < probability P (fun ω => U ω = u)) :
    conditionalProbability P B (fun ω => U ω = u) ≤ b := by
  have hu' : 0 < (toCompatFiniteLaw P).prob (fun ω => U ω = u) := by
    simpa only [toCompatFiniteLaw_probability] using hu
  have hb := FiniteLaw.coarse_total_probability_bound (toCompatFiniteLaw P)
    Z U g hU u hu' B (fun _ => b)
    (by simpa only [toCompatFiniteLaw_probability,
      toCompatFiniteLaw_conditionalProbability] using h)
  rw [← Finset.sum_mul, FiniteLaw.sum_conditional_atom_prob _ _ hu', one_mul,
    toCompatFiniteLaw_conditionalProbability] at hb
  exact hb

end RiffleUpperV2
