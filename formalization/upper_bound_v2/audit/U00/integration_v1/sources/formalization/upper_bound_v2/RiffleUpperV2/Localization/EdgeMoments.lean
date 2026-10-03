import RiffleUpperV2.Localization.Edges
import RiffleUpperV2.Localization.CylinderAdapters

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

theorem probability_at_most_one {Ω : Type*} [Fintype Ω] (P : PMF Ω) (E : Ω → Prop) :
    probability P E ≤ 1 := by
  have h := RiffleLowerV2.Thinning.expect_mono P
    (f := fun ω => if E ω then (1:ℝ) else 0) (g := fun _ => (1:ℝ))
    (fun ω => by split_ifs <;> norm_num)
  change RiffleLowerV2.expect P (fun ω => if E ω then (1:ℝ) else 0) ≤ 1
  simpa only [RiffleLowerV2.Model.expect_const] using h

theorem sum_edge_probabilities {Ω I : Type*} [Fintype Ω] [DecidableEq I]
    (P : PMF Ω) (edges : Ω → Finset I) (slots : Finset I) :
    ∑ m ∈ slots, probability P (fun ω => m ∈ edges ω) =
      expect P (fun ω => ((slots ∩ edges ω).card : ℝ)) := by
  simp only [RiffleUpperV2.probability, RiffleLowerV2.probability,
    RiffleUpperV2.expect, RiffleLowerV2.expect, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.mul_sum]
  have he : slots ∩ edges ω = slots.filter (fun i => i ∈ edges ω) := by
    ext i
    simp
  rw [he, Finset.sum_filter]
  simp

theorem sum_edge_probabilities_le {Ω I : Type*} [Fintype Ω] [DecidableEq I]
    (P : PMF Ω) (edges : Ω → Finset I) (slots : Finset I) :
    ∑ m ∈ slots, probability P (fun ω => m ∈ edges ω) ≤
      expect P (fun ω => ((edges ω).card : ℝ)) := by
  rw [sum_edge_probabilities]
  apply RiffleLowerV2.Thinning.expect_mono
  intro ω
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : slots ∩ edges ω ⊆ edges ω)

theorem expected_anchoredEdges_le_mean {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) :
    expect (fixedCountPMF cuts) (fun ω => ((anchoredEdges c₀ R x ω).card : ℝ)) ≤ anchoredMean cuts R x := by
  rw [← prefixRows_expect cuts hn]
  apply RiffleLowerV2.Thinning.expect_mono
  intro ω
  exact_mod_cast anchoredEdges_card_le_occupancy c₀ R x ω

/-- The source terminal density bound; it holds in fact for every prefix block. -/
theorem terminalDensity {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (slots : Finset ℤ) :
    anchoredDensity cuts c₀ R x slots ≤ anchoredMean cuts R x := by
  apply terminalDensity_of_expected_count slots (anchoredEdgeProbability cuts c₀ R x)
  · intro m _
    exact ⟨RiffleLowerV2.Thinning.probability_nonneg _ _, probability_at_most_one _ _⟩
  · exact (sum_edge_probabilities_le (fixedCountPMF cuts) (anchoredEdges c₀ R x) slots).trans
      (expected_anchoredEdges_le_mean cuts hn c₀ R x)

end RiffleUpperV2.Localization
