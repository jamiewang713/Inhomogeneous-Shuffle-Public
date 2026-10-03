import Contracts.v1.ModelThinning

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Targets
open TimeProfile

/-- LB03; the restriction R≤N prevents totalized zero denominators outside its domain. -/
def ExactJointFactorial : Prop :=
  ∀ {k N K d : ℕ} (cuts : Cuts k N K) (w : Fin d → Word k K) (r : Fin d → ℕ),
    Function.Injective w → (∑ i, r i) ≤ N →
    expect (fixedCountPMF cuts) (factorialProduct w r) = exactFactorial cuts w r

def RelativeJointFactorial : Prop :=
  ∀ c C : ℝ, 0 < c → 0 < C → ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ,
    ∀ N ≥ N0, ∀ k K d : ℕ, (K : ℝ) ≤ C * logScale N →
    ∀ (cuts : Cuts k N K) (w : Fin d → Word k K) (r : Fin d → ℕ),
      Function.Injective w → (∀ i j, c * N ≤ (cuts.count j ((w i).get j) : ℝ)) →
      ((∑ i, r i) : ℝ) ≤ (N : ℝ)^(1/5 : ℝ) →
      |expect (fixedCountPMF cuts) (factorialProduct w r) -
        ∏ i, ((N : ℝ) * wordMass cuts (w i))^(r i)| ≤
      D * (K+1) * ((∑ i, r i) : ℝ)^2 / N *
        ∏ i, ((N : ℝ) * wordMass cuts (w i))^(r i)

def BonferroniSandwich : Prop :=
  ∀ m : ℕ, 2 ≤ m → Even m → ∀ n : ℕ,
    0 ≤ bonferroni m n - (if 2 ≤ n then 1 else 0) ∧
    bonferroni m n - (if 2 ≤ n then 1 else 0) ≤ bonferroniRemainder m n

def BonferroniProduct : Prop :=
  ∀ m : ℕ, 2 ≤ m → Even m → ∀ x y : ℕ,
    0 ≤ bonferroni m x * bonferroni m y - (if 2 ≤ x ∧ 2 ≤ y then 1 else 0) ∧
    bonferroni m x * bonferroni m y - (if 2 ≤ x ∧ 2 ≤ y then 1 else 0) ≤
      bonferroniRemainder m x + bonferroniRemainder m y +
      bonferroniRemainder m x * bonferroniRemainder m y

def CentralComparison : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (P : PMF Ω) (X Y : Ω → ℕ) (μ ν ε : ℝ) (m : ℕ),
    0 < μ → 0 < ν → 0 ≤ ε → ε ≤ 1 → 2 ≤ m → Even m →
    (∀ r s : ℕ, r+s ≤ 2*m →
      |expect P (fun ω => falling (X ω) r * falling (Y ω) s) - μ^r * ν^s| ≤ ε * μ^r * ν^s) →
    |probability P (fun ω => 2 ≤ X ω ∧ 2 ≤ Y ω) - poissonCollision μ * poissonCollision ν| ≤
      ε * (1+μ) * (1+ν) * Real.exp (μ+ν) +
      3 * (poissonRemainder m μ + poissonRemainder m ν + poissonRemainder m μ * poissonRemainder m ν)

def CentralComparisonOne : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (P : PMF Ω) (X : Ω → ℕ) (μ ε : ℝ) (m : ℕ),
    0 < μ → 0 ≤ ε → ε ≤ 1 → 2 ≤ m → Even m →
    (∀ r : ℕ, r ≤ m → |expect P (fun ω => falling (X ω) r) - μ^r| ≤ ε * μ^r) →
    |probability P (fun ω => 2 ≤ X ω) - poissonCollision μ| ≤
      ε * (1+μ) * Real.exp μ + 3 * poissonRemainder m μ

def RareSandwich : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (P : PMF Ω) (X : Ω → ℕ),
    expect P (fun ω => falling (X ω) 2) / 2 - expect P (fun ω => falling (X ω) 3) / 3 ≤
      probability P (fun ω => 2 ≤ X ω) ∧
    probability P (fun ω => 2 ≤ X ω) ≤ expect P (fun ω => falling (X ω) 2) / 2

/-- LB08: actual-model relative marginal/pair errors and variance; no moment premises. -/
def UniformOccupancy : Prop :=
  ∀ c C : ℝ, 0 < c → 0 < C → ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ,
    ∀ N ≥ N0, ∀ k K : ℕ, (K : ℝ) ≤ C * logScale N →
    ∀ (cuts : Cuts k N K) (W : Finset (Word k K)), selectedPiles cuts W c →
      (∀ w ∈ W,
        |probability (fixedCountPMF cuts) (collisionEvent w) - poissonCollision (N * wordMass cuts w)| ≤
          D * (N : ℝ)^(-1/100 : ℝ) * poissonCollision (N * wordMass cuts w)) ∧
      (∀ w ∈ W, ∀ v ∈ W, w ≠ v →
        |probability (fixedCountPMF cuts) (fun ω => collisionEvent w ω ∧ collisionEvent v ω) -
          probability (fixedCountPMF cuts) (collisionEvent w) * probability (fixedCountPMF cuts) (collisionEvent v)| ≤
        D * (N : ℝ)^(-1/100 : ℝ) * probability (fixedCountPMF cuts) (collisionEvent w) *
          probability (fixedCountPMF cuts) (collisionEvent v)) ∧
      variance (fixedCountPMF cuts) (collisionCount W) ≤ expect (fixedCountPMF cuts) (collisionCount W) +
        D * (N : ℝ)^(-1/100 : ℝ) * (expect (fixedCountPMF cuts) (collisionCount W))^2

end RiffleLowerV2.Targets
