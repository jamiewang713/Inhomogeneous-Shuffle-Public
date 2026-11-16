import Shuffle.Conditioning
import Shuffle.HypergeometricBoundary
import Shuffle.HypergeometricConcentration
import Shuffle.HypergeometricAntiConcentration

/-! Exact conditional-law transfer of the frozen hypergeometric results. -/

noncomputable section

namespace Shuffle
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Equality of all conditional count probabilities with the canonical law.
The conclusions below apply on positive events only; this definition introduces
no arbitrary probability law on a null event. -/
def HasConditionalHypergeometric (p : FiniteLaw Ω) (E : Ω → Prop)
    (Y : Ω → ℕ) (h : HypergeomParams) : Prop :=
  ∀ q : ℕ, p.conditionalProb E (fun ω => Y ω = q) = h.pointMass q

theorem conditional_hypergeom_expect (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams)
    (hlaw : p.HasConditionalHypergeometric E Y h) :
    p.conditionalExpect E (fun ω => (Y ω : ℝ)) = h.mean := by
  rw [p.conditional_expect_eq_of_count_law E hE Y h.draws h.law hlaw
    (fun n : ℕ => (n : ℝ))]
  exact h.expect_val

theorem conditional_hypergeom_descFactorial (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams)
    (hlaw : p.HasConditionalHypergeometric E Y h) (r : ℕ) :
    p.conditionalExpect E (fun ω => ((Y ω).descFactorial r : ℝ)) =
      (h.marked.descFactorial r : ℝ) * (h.draws.descFactorial r : ℝ) /
        (h.population.descFactorial r : ℝ) := by
  rw [p.conditional_expect_eq_of_count_law E hE Y h.draws h.law hlaw
    (fun n : ℕ => (n.descFactorial r : ℝ))]
  exact h.expect_descFactorial r

theorem conditional_hypergeom_variance (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams)
    (hlaw : p.HasConditionalHypergeometric E Y h) :
    (p.condition E hE).variance (fun ω => (Y ω : ℝ)) = h.varianceFormula := by
  rw [p.conditional_variance_eq_of_count_law E hE Y h.draws h.law hlaw]
  exact h.variance_val

theorem conditional_hypergeom_centered_second (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams)
    (hlaw : p.HasConditionalHypergeometric E Y h) :
    p.conditionalExpect E (fun ω => ((Y ω : ℝ) - h.mean) ^ 2) =
      h.varianceFormula := by
  rw [p.conditional_expect_eq_of_count_law E hE Y h.draws h.law hlaw
    (fun n : ℕ => ((n : ℝ) - h.mean) ^ 2)]
  rw [← h.variance_val]
  unfold variance
  rw [h.expect_val]

theorem conditional_hypergeom_variance_eq_zero_iff (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams)
    (hlaw : p.HasConditionalHypergeometric E Y h) :
    (p.condition E hE).variance (fun ω => (Y ω : ℝ)) = 0 ↔
      h.marked = 0 ∨ h.draws = 0 ∨ h.marked = h.population ∨
        h.draws = h.population := by
  rw [p.conditional_hypergeom_variance E hE Y h hlaw, ← h.variance_val]
  exact h.variance_eq_zero_iff

theorem conditional_hypergeom_zero_centered_tail (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams)
    (hlaw : p.HasConditionalHypergeometric E Y h) (hv : h.varianceFormula = 0)
    {t : ℝ} (ht : 0 < t) :
    p.conditionalProb E (fun ω => t ≤ |(Y ω : ℝ) - h.mean|) = 0 := by
  rw [p.conditional_prob_eq_of_count_law E hE Y h.draws h.law hlaw
    (fun n : ℕ => t ≤ |(n : ℝ) - h.mean|)]
  exact h.centered_tail_zero hv ht

theorem conditional_hypergeom_pointMass_le (p : FiniteLaw Ω) (E : Ω → Prop)
    (_hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams)
    (hlaw : p.HasConditionalHypergeometric E Y h) (hv : 0 < h.varianceFormula)
    (q : ℕ) :
    p.conditionalProb E (fun ω => Y ω = q) ≤ 4 / Real.sqrt h.varianceFormula := by
  rw [hlaw q]
  exact h.pointMass_le_four_div_sqrt hv q

theorem conditional_hypergeom_pow_le (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams)
    (hlaw : p.HasConditionalHypergeometric E Y h) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    p.conditionalExpect E (fun ω => s ^ Y ω) ≤
      (1 - (h.draws : ℝ) / h.population +
        ((h.draws : ℝ) / h.population) * s) ^ h.marked := by
  rw [p.conditional_expect_eq_of_count_law E hE Y h.draws h.law hlaw]
  exact h.expect_pow_le hs hs1

/-- One concentration constant works for every finite conditional count law.
Only positive conditioning events are quantified. -/
theorem exists_conditional_hypergeom_concentration_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : FiniteLaw Ω) (E : Ω → Prop)
      (_hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams),
      p.HasConditionalHypergeometric E Y h → ∀ t : ℝ, 0 ≤ t →
      p.conditionalProb E (fun ω => t ≤ |(Y ω : ℝ) - h.mean|) ≤
        2 * Real.exp (-c * min (t ^ 2 / (h.mean + t)) t) := by
  obtain ⟨c, hc, hbound⟩ := HypergeomParams.exists_concentration_constant
  refine ⟨c, hc, ?_⟩
  intro p E hE Y h hlaw t ht
  rw [p.conditional_prob_eq_of_count_law E hE Y h.draws h.law hlaw
    (fun n : ℕ => t ≤ |(n : ℝ) - h.mean|)]
  exact hbound h t ht

/-- The universal anti-concentration constant is independent of the reveal
event, the ambient finite law, and the hypergeometric parameters. -/
theorem exists_conditional_hypergeom_pointMass_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : FiniteLaw Ω) (E : Ω → Prop)
      (_hE : 0 < p.prob E) (Y : Ω → ℕ) (h : HypergeomParams),
      p.HasConditionalHypergeometric E Y h → 0 < h.varianceFormula →
      ∀ q : ℕ, p.conditionalProb E (fun ω => Y ω = q) ≤
        C / Real.sqrt h.varianceFormula := by
  refine ⟨4, by norm_num, ?_⟩
  intro p E hE Y h hlaw hv q
  exact p.conditional_hypergeom_pointMass_le E hE Y h hlaw hv q

end FiniteLaw
end Shuffle
