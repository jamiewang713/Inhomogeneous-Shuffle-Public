import RiffleUpperV2.Shared.Random

/-! Exact candidate endpoint specifications; none is asserted as proved. -/
noncomputable section
open Set Filter
open scoped ENNReal
namespace RiffleUpperV2.Contracts.V1
open TimeProfile

def P : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T η : ℝ, 0 < T → 0 < η →
  ∃ χ0 : ℝ, 0 < χ0 ∧ ∀ χ : ℝ, 0 < χ → χ ≤ χ0 →
  ∀ P : BorelPartition k, P.IsRegular χ (regularityConstant k) →
  ∀ g γ : ℝ, 0 < g → g < 1/(k : ℝ) → 0 < γ →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∃ φ0 : ℝ, 0 < φ0 ∧ ∀ φ : ℝ, 0 < φ → φ ≤ φ0 →
  ∀ μ : TimeLaw k, ScalarIntegrable μ P T → reducedMargin μ T ≤ -η →
  ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
  ∀ (N : ℕ) (hN : N0 ≤ N) (cuts : Cuts k N (horizonDepth N T)),
    AlmostLike cuts (by omega) μ P T ρ φ →
    LocalGood cuts (by omega) g γ ρ 0 T →
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤ ε

def T : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ (μ : TimeLaw k) (cuts : ∀ N : ℕ, InfiniteCuts k N),
  ArbitrarilyFineApproximation μ cuts →
  (∀ t : ℝ, 0 ≤ t → criticalTime μ < ENNReal.ofReal t →
    Tendsto (fun N => tv (physicalInverseLaw ((cuts N).take (horizonDepth N t)))
      (uniformPermutation N)) atTop (nhds 0)) ∧
  (∀ ε : ℝ, 0 < ε → ε < 1 →
    limsup (fun N => mixingTime (cuts N) ε / ENNReal.ofReal (Real.log (N : ℝ))) atTop
      ≤ criticalTime μ)

/-- The empirical random-environment consequence uses one common deterministic mesh. -/
def REmpirical : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T η0 g0 γ0 : ℝ,
  0 < T → 0 < η0 → 0 < g0 → 0 < γ0 →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∀ (K : ℕ → ℕ), (∀ N, 2 ≤ N → (K N : ℝ) ≤ T * Real.log (N : ℝ)) →
  ∀ (Q : ∀ N, PMF (Cuts k N (K N))),
    Tendsto (fun N => probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N,
      EmpiricalNegativeMargin N 0 cuts (by omega) η0 ∧
      LocalGood cuts (by omega) g0 γ0 ρ 0 ((K N : ℝ) / Real.log (N : ℝ))))
      atTop (nhds 1) →
    Tendsto (fun N => tv (randomInverseLaw (Q N)) (uniformPermutation N)) atTop (nhds 0)

def RProfile : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T η : ℝ, 0 < T → 0 < η →
  ∃ χ0 : ℝ, 0 < χ0 ∧ ∀ χ : ℝ, 0 < χ → χ ≤ χ0 →
  ∀ P : BorelPartition k, P.IsRegular χ (regularityConstant k) →
  ∀ g γ : ℝ, 0 < g → g < 1/(k : ℝ) → 0 < γ →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∃ φ0 : ℝ, 0 < φ0 ∧ ∀ φ : ℝ, 0 < φ → φ ≤ φ0 →
  ∀ μ : TimeLaw k, ScalarIntegrable μ P T → reducedMargin μ T ≤ -η →
  ∀ Q : ∀ N, PMF (Cuts k N (horizonDepth N T)),
    Tendsto (fun N => probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N, AlmostLike cuts (by omega) μ P T ρ φ)) atTop (nhds 1) →
    Tendsto (fun N => probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N, LocalGood cuts (by omega) g γ ρ 0 T)) atTop (nhds 1) →
    Tendsto (fun N => tv (randomInverseLaw (Q N)) (uniformPermutation N)) atTop (nhds 0)

/-- The finite quantitative mixture statement preceding its convergence corollary. -/
def REmpiricalBound : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T η0 g0 γ0 : ℝ,
  0 < T → 0 < η0 → 0 < g0 → 0 < γ0 →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
  ∀ (N : ℕ) (hN : N0 ≤ N) (K : ℕ), (K : ℝ) ≤ T * Real.log (N : ℝ) →
  ∀ Q : PMF (Cuts k N K),
    tv (randomInverseLaw Q) (uniformPermutation N) ≤
      probability Q (fun cuts => ¬(EmpiricalNegativeMargin N 0 cuts (by omega) η0 ∧
        LocalGood cuts (by omega) g0 γ0 ρ 0 ((K : ℝ) / Real.log (N : ℝ)))) +
      (N : ℝ)^(-c)

def R : Prop := REmpiricalBound ∧ REmpirical ∧ RProfile

end RiffleUpperV2.Contracts.V1
