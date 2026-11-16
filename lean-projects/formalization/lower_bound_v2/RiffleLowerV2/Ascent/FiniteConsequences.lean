import RiffleLowerV2.Ascent.UniformBaseline
import RiffleLowerV2.Ascent.Selection

/-! Finite consequences with their analytic inputs made explicit.
The concrete lane entry point must supply the proved concentration and expectation. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Ascent

theorem uniformScan_of_concentration (hc : Targets.ComponentConcentration) : Targets.UniformScan := by
  intro N H0 s hM hs
  have hMr : (0 : ℝ) < H0.card := by exact_mod_cast hM
  have hq (q : Fin (N+1)) : probability (uniformPermutation N)
      (fun π => ((internalEdges (clipTranslate N H0 q.val)).card : ℝ)/2+s <
        (ascentCount (clipTranslate N H0 q.val) π : ℝ)) ≤ Real.exp (-s^2/H0.card) := by
    have ht := (hc N ∅ (clipTranslate N H0 q.val) H0.card s hMr
      (by exact_mod_cast clipTranslate_card_le N H0 q.val) hs).1
    simp only [componentSort_empty, expect_ascentCount_uniform] at ht
    refine (probability_mono (uniformPermutation N) ?_).trans ht
    intro π hp
    linarith
  calc
    _ ≤ ∑ q : Fin (N+1), probability (uniformPermutation N)
      (fun π => ((internalEdges (clipTranslate N H0 q.val)).card : ℝ)/2+s <
        (ascentCount (clipTranslate N H0 q.val) π : ℝ)) := probability_iUnion_le _ _
    _ ≤ ∑ _q : Fin (N+1), Real.exp (-s^2/H0.card) :=
      Finset.sum_le_sum fun q _ => hq q
    _ = _ := by simp

theorem componentComparison_of_concentration_expectation
    (hc : Targets.ComponentConcentration) (he : Targets.ComponentExpectation) :
    Targets.ComponentComparison := by
  intro N G H M s hM hHM hs Δ hdelta
  have hE := he N G H
  have ht := (hc N G H M _ hM hHM hdelta).2
  refine (probability_mono (uniformPermutation N) ?_).trans ht
  intro π hp
  dsimp only [Δ] at hdelta
  dsimp only [Δ] at hp ⊢
  linarith

theorem componentConcentrationTwoSided_of_concentration
    (hc : Targets.ComponentConcentration) : Targets.ComponentConcentrationTwoSided := by
  intro N G H M t hM hHM ht
  obtain ⟨hu, hl⟩ := hc N G H M t hM hHM ht
  let X := fun π => (ascentCount H (componentSort G π) : ℝ)
  let E := expect (uniformPermutation N) X
  calc
    _ ≤ probability (uniformPermutation N) (fun π =>
      t ≤ X π-E ∨ X π-E ≤ -t) := by
        apply probability_mono
        intro π hπ
        rcases le_abs.mp hπ with h | h
        · exact Or.inl h
        · apply Or.inr
          dsimp [X, E]
          linarith
    _ ≤ probability (uniformPermutation N) (fun π => t ≤ X π-E) +
      probability (uniformPermutation N) (fun π => X π-E ≤ -t) := probability_union_le _ _ _
    _ ≤ Real.exp (-t^2/M) + Real.exp (-t^2/M) := add_le_add hu hl
    _ = _ := by ring

end RiffleLowerV2.Ascent
