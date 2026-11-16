import RiffleUpperV2.Localization.EdgeGeometry

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Localization

/-- Expected discarded edge count is bounded by the expected discarded rows. -/
theorem discardedEdges_expect_le_rows {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (W : Finset (Word k d)) :
    expect (fixedCountPMF cuts) (fun ω => ((edgesInWords c₀ R W ω).card : ℝ)) ≤
      expect (fixedCountPMF cuts) (fun ω => ((rowsInWords R W ω).card : ℝ)) := by
  apply RiffleLowerV2.Thinning.expect_mono
  intro ω
  exact_mod_cast edgesInWords_card_le_rows c₀ R W ω

theorem discardedEdges_total_le_rows {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (W : Finset (Word k d)) (slots : Finset ℤ) :
    (∑ m ∈ slots, probability (fixedCountPMF cuts) (fun ω => m ∈ edgesInWords c₀ R W ω)) ≤
      expect (fixedCountPMF cuts) (fun ω => ((rowsInWords R W ω).card : ℝ)) :=
  (sum_edge_probabilities_le _ _ _).trans (discardedEdges_expect_le_rows cuts c₀ R W)

/-- Discarded full words contribute no more than their expected row mass to any
finite square-sum of edge marginals. -/
theorem discardedEdges_density_le_rows {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (W : Finset (Word k d)) (slots : Finset ℤ) :
    (∑ m ∈ slots, probability (fixedCountPMF cuts) (fun ω => m ∈ edgesInWords c₀ R W ω)^2) ≤
      expect (fixedCountPMF cuts) (fun ω => ((rowsInWords R W ω).card : ℝ)) := by
  apply (density_le_total slots (fun m => probability (fixedCountPMF cuts)
    (fun ω => m ∈ edgesInWords c₀ R W ω)) (fun _ _ =>
      ⟨RiffleLowerV2.Thinning.probability_nonneg _ _,probability_at_most_one _ _⟩)).trans
  exact (sum_edge_probabilities_le _ _ _).trans (discardedEdges_expect_le_rows cuts c₀ R W)

end RiffleUpperV2.Localization
