import Contracts.v1.FactorialOccupancy

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Targets

/-- LB04: only the actual component ascent statistic, never generic block differences. -/
def ComponentConcentration : Prop :=
  ∀ (N : ℕ) (G : PathEdges N) (H : Finset (Fin N)) (M t : ℝ),
    0 < M → (H.card : ℝ) ≤ M → 0 < t →
    let X := fun π => (ascentCount H (componentSort G π) : ℝ)
    let E := expect (uniformPermutation N) X
    probability (uniformPermutation N) (fun π => t ≤ X π - E) ≤ Real.exp (-t^2/M) ∧
    probability (uniformPermutation N) (fun π => X π - E ≤ -t) ≤ Real.exp (-t^2/M)

def ComponentExpectation : Prop :=
  ∀ (N : ℕ) (G : PathEdges N) (H : Finset (Fin N)),
    expect (uniformPermutation N) (fun π => (ascentCount H (componentSort G π) : ℝ)) ≥
      ((internalEdges H).card : ℝ)/2 + ((G ∩ internalEdges H).card : ℝ)/6 - (boundary H).card

def UniformScan : Prop :=
  ∀ (N : ℕ) (H0 : Finset ℤ) (s : ℝ), 0 < H0.card → 0 < s →
    probability (uniformPermutation N) (scan H0 s) ≤ (N+1) * Real.exp (-s^2/H0.card)

def ComponentComparison : Prop :=
  ∀ (N : ℕ) (G : PathEdges N) (H : Finset (Fin N)) (M s : ℝ),
    0 < M → (H.card : ℝ) ≤ M → 0 < s →
    let Δ := ((G ∩ internalEdges H).card : ℝ)/6 - (boundary H).card - s
    0 < Δ → probability (uniformPermutation N)
      (fun π => (ascentCount H (componentSort G π) : ℝ) ≤ ((internalEdges H).card : ℝ)/2+s) ≤
      Real.exp (-Δ^2/M)

/-- Uniform asymptotic graph comparison, with deterministic geometry as legitimate inputs. -/
def UniformGraphScan : Prop :=
  ∀ a δ D ε : ℝ, 0 < a → 0 < δ → 0 ≤ D → 0 < ε →
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (H0 : Finset ℤ) (G : PathEdges N),
      (N : ℝ)^a ≤ (H0.card : ℝ) →
      (∀ q : Fin (N+1), ((boundary (clipTranslate N H0 q.val)).card : ℝ) ≤ D * Real.sqrt H0.card) →
      (∃ q : Fin (N+1), ((G ∩ internalEdges (clipTranslate N H0 q.val)).card : ℝ) ≥
        (H0.card : ℝ)^(1/2+δ)) →
      probability (uniformPermutation N)
        (fun π => scan H0 ((H0.card : ℝ)^(1/2+δ/2)) (componentSort G π)) ≥ 1-ε

end RiffleLowerV2.Targets
