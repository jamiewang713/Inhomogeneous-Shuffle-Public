import RiffleMain.RandomLower.Basic
import RiffleLowerV2.EmpiricalLower.LargestAsymptotic

noncomputable section
set_option autoImplicit false
open scoped Topology
open RiffleLowerV2 TimeProfile Filter
open RiffleLowerV2.EmpiricalLower
namespace RiffleMain.RandomLower

/-- Event-level form of the proved largest-word test, before taking total variation. -/
theorem largest_run_success {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (m : ℕ) (hm : 1 ≤ m) (hmean : (m : ℝ) ≤ maximalMean cuts hN/2) :
    1-Real.exp (-chernoffConstant*maximalMean cuts hN) ≤
      probability (physicalInverseLaw cuts) (fun π => HasIncreasingRun π m) := by
  obtain ⟨w, _hw, _hwmean, htail⟩ := Thinning.maximalWordTail cuts hN
  have hgood : 1-Real.exp (-chernoffConstant*maximalMean cuts hN) ≤
      probability (fixedCountPMF cuts) (fun ω => m ≤ wordCount w ω) := by
    have hc := Ascent.probability_not (fixedCountPMF cuts) (fun ω => wordCount w ω < m)
    simp only [not_lt] at hc
    rw [hc]
    exact sub_le_sub_left (htail m hmean) 1
  rw [Model.physicalMatrixBridge]
  have hmap : probability (matrixLaw cuts) (fun π => HasIncreasingRun π m) =
      probability (fixedCountPMF cuts) (fun ω => HasIncreasingRun (stableSort ω) m) := by
    unfold matrixLaw probability
    exact Model.expect_map _ _ _
  rw [hmap]
  apply hgood.trans
  apply Ascent.probability_mono
  intro ω hω
  exact fullWord_forces_increasingRun ω w m hm hω

/-- The run event is identical for all arrays satisfying the largest-word margin. -/
theorem largest_common_event (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ k K : ℕ,
      ∀ (cuts : Cuts k N K) (hN : 2 ≤ N),
      b ≤ beta cuts (Targets.deckPos hN) (horizon N K) →
      1-ε ≤ probability (physicalInverseLaw cuts)
        (fun π => HasIncreasingRun π (largestRunLength N b)) := by
  obtain ⟨N0, hN0, hscales⟩ := largestMean_uniform_scales b ε hb hε
  refine ⟨N0, hN0, ?_⟩
  intro N hlarge k K cuts hN hmargin
  have hmean : (N : ℝ)^b ≤ maximalMean cuts (Targets.deckPos hN) := by
    rw [Thinning.maximalMean_eq_rpow_beta hN cuts]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hmargin
  obtain ⟨hm, _, hmMu, herr⟩ := hscales N hlarge _ hmean
    (maximalMean_le_population cuts (Targets.deckPos hN))
  have hs := largest_run_success cuts (Targets.deckPos hN) (largestRunLength N b)
    (by omega) hmMu
  have hnonneg : 0 ≤ largestRunError N b := by unfold largestRunError; positivity
  linarith

end RiffleMain.RandomLower
