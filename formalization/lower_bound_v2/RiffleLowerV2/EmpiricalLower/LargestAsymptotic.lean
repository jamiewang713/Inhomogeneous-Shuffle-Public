import RiffleLowerV2.EmpiricalLower.LargestFinite
import RiffleLowerV2.EmpiricalLower.LargestAsymptotic.Numerical

noncomputable section
namespace RiffleLowerV2.EmpiricalLower
open TimeProfile Targets

/-- A uniform largest-word endpoint from the actual finite mean alone.
The prescribed floor length and both finite errors are discharged uniformly. -/
theorem largestMean_uniform (b epsilon : ℝ) (hb : 0 < b) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ k K : ℕ,
      ∀ (cuts : Cuts k N K) (hN : 0 < N),
      (N : ℝ)^b ≤ maximalMean cuts hN →
      1-epsilon ≤ tv (physicalInverseLaw cuts) (uniformPermutation N) := by
  obtain ⟨N0, hN02, hscales⟩ := largestMean_uniform_scales b epsilon hb hepsilon
  refine ⟨N0, hN02, ?_⟩
  intro N hN k K cuts hpos hmean
  obtain ⟨hm2, hmN, hmMu, herror⟩ :=
    hscales N hN (maximalMean cuts hpos) hmean (maximalMean_le_population cuts hpos)
  have htv := finiteLargestWordTV cuts hpos (largestRunLength N b) hm2 hmN hmMu
  change Real.exp (-chernoffConstant*maximalMean cuts hpos) +
    ((N-largestRunLength N b+1 : ℕ) : ℝ) / ((largestRunLength N b).factorial : ℝ)
    ≤ epsilon at herror
  linarith

/-- Source `prop:largest-prefix`: the frozen physical-law largest-margin endpoint,
with no local-good, profile-law, witness, or stochastic premise. -/
theorem largestOnly : Targets.LargestOnlyTarget := by
  intro k _ T etaLargest _ heta epsilon hepsilon
  obtain ⟨N0, hN02, huniform⟩ := largestMean_uniform etaLargest epsilon heta hepsilon
  refine ⟨N0, hN02, ?_⟩
  intro N hN hlarge cuts hmargin
  apply huniform N hlarge k (horizonDepth N T) cuts (deckPos hN)
  rw [Thinning.maximalMean_eq_rpow_beta hN cuts]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) hmargin

end RiffleLowerV2.EmpiricalLower
