import RiffleUpperV2.Shared.Conditioning
import RiffleUpperV2.Exploration.Objects

/-! The good histories below are literal functions of the sampled matrices.
The concentration constants are chosen before arrays and their estimate is
a conclusion, so no unproved event certificate is an endpoint premise. -/
noncomputable section
namespace RiffleUpperV2.Contracts.V1
open Exploration

/-- Source: lem:ub-conditional-first-moment, together with its specified H bound.
The positive-fiber assertion includes time zero. The terminal count is zero. -/
def C : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T η g γ : ℝ,
  0 < T → 0 < η → η ≤ 1 → 0 < g → g < 1/(k : ℝ) → 0 < γ → γ ≤ 1 →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∃ A cH ζ C : ℝ, 0 < A ∧ 0 < cH ∧ 0 < ζ ∧ 0 < C ∧
  ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
  ∀ (N : ℕ) (hN : N0 ≤ N) (L : ℕ), ((L+1 : ℕ) : ℝ) ≤ T * Real.log (N : ℝ) →
  ∀ cuts : Cuts k N (L+1),
    EmpiricalNegativeMargin N 0 cuts (by omega) (2*η) →
    integerWindowGood N cuts (by omega) ρ γ g →
    retainedGoodCluster cuts (by omega) (clusterSpan γ) g →
    probability (fixedCountPMF cuts)
      (fun ω => ¬ concentrationEvent cuts (clusterSpan γ) g (η/10) ω) ≤
        badBound N (η/10) A cH ∧
    (∀ (p : Fin k) (d : Direction), (N : ℝ)^(η/10) ≤ (pileSize cuts p : ℝ) →
      ∀ i : ℕ, i ≤ pileSize cuts p → ∀ ω : Sample cuts × Sample cuts,
      0 < probability (independentPairLaw cuts)
        (fun v => pairHistory cuts p d i v = pairHistory cuts p d i ω) →
      pairHistoryGood cuts (clusterSpan γ) g (η/10)
        (Real.sqrt (badBound N (η/10) A cH)) p d i ω →
      conditionalExpect (independentPairLaw cuts)
        (fun v => (remainingDirectionalCount cuts (clusterSpan γ) g (η/10) p d i v.1 v.2 : ℝ))
        (fun v => pairHistory cuts p d i v = pairHistory cuts p d i ω) ≤ C*(N : ℝ)^(-ζ)) ∧
    (∀ (p : Fin k) (d : Direction) (ω ω' : Sample cuts),
      remainingDirectionalCount cuts (clusterSpan γ) g (η/10) p d (pileSize cuts p) ω ω' = 0)

end RiffleUpperV2.Contracts.V1
