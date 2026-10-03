import RiffleUpperV2.Shared.Empirical

/-! Candidate exact specifications. These definitions are not proofs of F or E. -/
noncomputable section
namespace RiffleUpperV2.Contracts.V1
open TimeProfile

/-- Source: prop:ub-empirical-first-moment. Original N and current n are distinct. -/
def F : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (T η g : ℝ), 0 < T → 0 < η → 0 < g → g < 1 / (k : ℝ) →
  ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
  ∀ (N : ℕ), N0 ≤ N → ∀ (n : ℕ) (hn : 2 ≤ n), n ≤ N →
  ∀ (a K : ℕ), a < K → (K : ℝ) ≤ T * Real.log (N : ℝ) →
  ∀ cuts : Cuts k n (K-a),
    FirstColumnGood cuts (by omega) g →
    EmpiricalNegativeMargin N a cuts (by omega) η →
    expectedCommonEdges cuts ≤ (N : ℝ) ^ (-c)

/-- Source: thm:ub-empirical-upper. No probabilistic estimates are premises. -/
def E : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (T η0 g0 γ0 : ℝ),
  0 < T → 0 < η0 → 0 < g0 → 0 < γ0 →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
  ∀ (N : ℕ) (hN : N0 ≤ N) (K : ℕ), (K : ℝ) ≤ T * Real.log (N : ℝ) →
  ∀ cuts : Cuts k N K,
    EmpiricalNegativeMargin N 0 cuts (by omega) η0 →
    LocalGood cuts (by omega) g0 γ0 ρ 0 ((K : ℝ) / Real.log (N : ℝ)) →
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤ (N : ℝ) ^ (-c)

end RiffleUpperV2.Contracts.V1
