import RiffleUpperV2.Localization.CollisionMass
import RiffleUpperV2.Localization.SmoothingDensity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

/-- Unconditional small-block density, directly from the two-row future collision
calculation. This holds without a minimum mean or a positive fluctuation. -/
theorem smallDensity {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (slots : Finset ℤ) :
    anchoredDensity cuts c₀ R x slots ≤
      anchoredMean cuts R x^4 * tailSquareMass cuts x^2 / 4 := by
  apply smallDensity_of_expected_edges slots (anchoredEdgeProbability cuts c₀ R x)
  · intro m _
    exact RiffleLowerV2.Thinning.probability_nonneg _ _
  · exact (sum_edge_probabilities_le (fixedCountPMF cuts) (anchoredEdges c₀ R x) slots).trans
      (expected_anchoredEdges_le_collision cuts c₀ R x)

/-- Actual large-block density after one endpoint atom factor and the exact
restricted two-row collision calculation. It also applies when x is the join. -/
theorem largeDensity {k n d : ℕ} (cuts : Cuts k n d) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (c₀ : ℤ) (R : Finset (Fin n)) {g χ : ℝ} {y z v x : Prefix k d}
    (hg : Reserve R g) (hpair : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x)
    (slots : Finset ℤ) :
    anchoredDensity cuts c₀ R x slots ≤
      4*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v)) *
        anchoredMean cuts R x^4 * tailSquareMass cuts x^2 +
      6*(slots.card : ℝ)*Real.exp (-RiffleLowerV2.chernoffConstant*g*sideScale cuts R v) := by
  have hE : 0 ≤ expect (fixedCountPMF cuts) (fun ω => ((anchoredEdges c₀ R x ω).card : ℝ)) :=
    RiffleLowerV2.Thinning.expect_nonneg _ (fun _ => Nat.cast_nonneg _)
  have hsq := pow_le_pow_left₀ hE (expected_anchoredEdges_le_collision cuts c₀ R x) 2
  have hmul := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v)) by positivity)
  apply (densityFromSmoothing cuts hn hd c₀ R hg hpair hvx slots).trans
  convert add_le_add_right hmul
    (6*(slots.card : ℝ)*Real.exp (-RiffleLowerV2.chernoffConstant*g*sideScale cuts R v)) using 1 <;> ring

end RiffleUpperV2.Localization
