import RiffleUpperV2.Shared.FiniteLawAdapters

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Conditional
open RiffleLowerV2.Thinning.Compat

/-- Square Jensen for the actual conditional fine-atom weights on a positive
coarse history. Null fine atoms have zero weight automatically. -/
theorem conditionalSquareJensen {Ω Γ Δ : Type*}
    [Fintype Ω] [Fintype Γ] [Fintype Δ] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ) (g : Γ → Δ) (hU : ∀ ω, U ω = g (Z ω))
    (u : Δ) (hu : 0 < probability P (fun ω => U ω = u)) (E : Ω → Prop) :
    (conditionalProbability P E (fun ω => U ω = u))^2 ≤
      ∑ z, conditionalProbability P (fun ω => Z ω = z) (fun ω => U ω = u) *
        (conditionalProbability P E (fun ω => Z ω = z))^2 := by
  let p := toCompatFiniteLaw P
  have hu' : 0 < p.prob (fun ω => U ω = u) := by
    simpa only [p, toCompatFiniteLaw_probability] using hu
  let q : FiniteLaw Γ := {
    mass := fun z => p.conditionalProb (fun ω => U ω = u) (fun ω => Z ω = z)
    mass_nonneg := fun z => p.conditionalProb_nonneg _ _
    mass_sum := p.sum_conditional_atom_prob _ hu' Z }
  have hv := q.variance_nonneg (fun z => p.conditionalProb (fun ω => Z ω = z) E)
  rw [q.variance_eq] at hv
  have ht := p.coarse_total_probability Z U g hU u hu' E
  change p.conditionalProb (fun ω => U ω = u) E =
    q.expect (fun z => p.conditionalProb (fun ω => Z ω = z) E) at ht
  have hh : (p.conditionalProb (fun ω => U ω = u) E)^2 ≤
      q.expect (fun z => (p.conditionalProb (fun ω => Z ω = z) E)^2) := by
    rw [ht]
    linarith
  simpa only [q, p, FiniteLaw.expect,
    toCompatFiniteLaw_conditionalProbability] using hh

/-- Source eq:ub-one-history-jensen, for any finite edge family and a genuine
auxiliary refinement of the natural history. This is a finite conditional
expectation written with its exact conditional fine-atom weights. -/
theorem selfIntersectionJensen {Ω Γ Δ I : Type*}
    [Fintype Ω] [Fintype Γ] [Fintype Δ] [Fintype I] (P : PMF Ω)
    (Z : Ω → Γ) (U : Ω → Δ) (g : Γ → Δ) (hU : ∀ ω, U ω = g (Z ω))
    (u : Δ) (hu : 0 < probability P (fun ω => U ω = u)) (E : I → Ω → Prop) :
    (∑ e, (conditionalProbability P (E e) (fun ω => U ω = u))^2) ≤
      ∑ z, conditionalProbability P (fun ω => Z ω = z) (fun ω => U ω = u) *
        ∑ e, (conditionalProbability P (E e) (fun ω => Z ω = z))^2 := by
  calc
    _ ≤ ∑ e, ∑ z,
        conditionalProbability P (fun ω => Z ω = z) (fun ω => U ω = u) *
          (conditionalProbability P (E e) (fun ω => Z ω = z))^2 :=
      Finset.sum_le_sum fun e _ => conditionalSquareJensen P Z U g hU u hu (E e)
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

/-- The two observed histories receive separate self-intersection bounds. -/
theorem crossHistorySquareBound {I : Type*} [Fintype I] (q q' : I → ℝ) :
    (∑ e, q e * q' e) ≤ ((∑ e, (q e)^2) + ∑ e, (q' e)^2) / 2 := by
  have h : (∑ e, 2 * (q e * q' e)) ≤ ∑ e, ((q e)^2 + (q' e)^2) := by
    exact Finset.sum_le_sum fun e _ => by nlinarith [sq_nonneg (q e - q' e)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at h
  linarith

end RiffleUpperV2.Conditional
