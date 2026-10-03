import RiffleUpperV2.Localization.OffsetAtoms

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

private theorem probability_split {Ω : Type*} [Fintype Ω] (P : PMF Ω) (E S : Ω → Prop) :
    probability P E = probability P (fun ω => E ω ∧ S ω) + probability P (fun ω => E ω ∧ ¬S ω) := by
  unfold RiffleUpperV2.probability RiffleLowerV2.probability
  rw [← RiffleLowerV2.Thinning.expect_add]
  congr 1
  funext ω
  by_cases he : E ω <;> by_cases hs : S ω <;> simp [he,hs]

/-- Direct source density expression before the two-row collision substitution.
All atom, internal-history, and good/bad submeasure premises are discharged here. -/
theorem densityFromSmoothing {k n d : ℕ} (cuts : Cuts k n d) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (c₀ : ℤ) (R : Finset (Fin n)) {g χ : ℝ} {y z v x : Prefix k d}
    (hg : Reserve R g) (hpair : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x)
    (slots : Finset ℤ) :
    anchoredDensity cuts c₀ R x slots ≤
      (16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v))) *
        (expect (fixedCountPMF cuts) (fun ω => ((anchoredEdges c₀ R x ω).card : ℝ)))^2 +
      6*(slots.card : ℝ)*Real.exp (-RiffleLowerV2.chernoffConstant*g*sideScale cuts R v) := by
  let data := endpointSmoothing cuts (by omega) c₀ R hg hpair hvx
  let a : ℤ → ℝ := fun m => probability (fixedCountPMF cuts)
    (fun ω => m ∈ anchoredEdges c₀ R x ω ∧ data.good ω)
  let b : ℤ → ℝ := fun m => probability (fixedCountPMF cuts)
    (fun ω => m ∈ anchoredEdges c₀ R x ω ∧ ¬data.good ω)
  let E : ℝ := expect (fixedCountPMF cuts) (fun ω => ((anchoredEdges c₀ R x ω).card : ℝ))
  let A : ℝ := 16*Real.sqrt (varianceDenominator χ v/(g*sideScale cuts R v))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := RiffleLowerV2.Thinning.expect_nonneg _ (fun _ => Nat.cast_nonneg _)
  have htotal : ∑ m ∈ slots, a m ≤ E := by
    calc
      _ ≤ ∑ m ∈ slots, anchoredEdgeProbability cuts c₀ R x m := by
        apply Finset.sum_le_sum
        intro m _
        exact RiffleLowerV2.Thinning.probability_mono _ (fun _ h => h.1)
      _ ≤ E := sum_edge_probabilities_le _ _ _
  have hfail : ∑ m ∈ slots, b m ≤ (slots.card : ℝ)*probability (fixedCountPMF cuts) (fun ω => ¬data.good ω) := by
    calc
      _ ≤ ∑ _m ∈ slots, probability (fixedCountPMF cuts) (fun ω => ¬data.good ω) := by
        apply Finset.sum_le_sum
        intro m _
        exact RiffleLowerV2.Thinning.probability_mono _ (fun _ h => h.2)
      _ = _ := by simp
  have hatom (m : ℤ) : a m ≤ A*E := by
    have h := goodEdge_atom cuts hn hd c₀ R hg hpair hvx m
    dsimp only at h
    dsimp only [a,A,E]
    simpa only [anchoredEdges_card] using h
  have hbase := largeDensity_of_atoms slots (anchoredEdgeProbability cuts c₀ R x) a b hA hE
    (fun m _ => ⟨RiffleLowerV2.Thinning.probability_nonneg _ _,probability_at_most_one _ _⟩)
    (fun m _ => RiffleLowerV2.Thinning.probability_nonneg _ _)
    (fun m _ => RiffleLowerV2.Thinning.probability_nonneg _ _)
    (fun m _ => probability_split _ _ _) (fun m _ => hatom m) htotal hfail
  have hf := data.failure
  have hmul := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg slots.card)
  change anchoredDensity cuts c₀ R x slots ≤ _ at hbase
  calc
    _ ≤ _ := hbase
    _ ≤ _ := by dsimp only [A,E] at *; nlinarith

end RiffleUpperV2.Localization
