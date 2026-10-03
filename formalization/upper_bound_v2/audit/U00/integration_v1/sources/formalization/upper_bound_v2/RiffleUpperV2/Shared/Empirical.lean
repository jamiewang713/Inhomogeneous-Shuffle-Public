import RiffleUpperV2.Shared.Model
import RiffleLowerV2.Shared.Empirical
import RiffleTimeProfile.Analysis

noncomputable section
open Set
namespace RiffleUpperV2
open TimeProfile

/-- Original N fixes the logarithmic scale; cuts contain n current labels. -/
def empiricalA {k n L : ℕ} (N a : ℕ) (cuts : Cuts k n L) (hn : 0 < n)
    (s u : ℕ) : ℝ :=
  RiffleLowerV2.gridSum N (fun j => maxCost (cuts.profile hn j)) (s-a) (u-a)

def empiricalB {k n L : ℕ} (N a : ℕ) (cuts : Cuts k n L) (hn : 0 < n)
    (θ : ℝ) (s u : ℕ) : ℝ :=
  RiffleLowerV2.gridSum N (fun j => psi (cuts.profile hn j) θ) (s-a) (u-a)

def empiricalBeta {k n L : ℕ} (N a : ℕ) (cuts : Cuts k n L) (hn : 0 < n)
    (s : ℕ) : ℝ :=
  Real.log (n : ℝ) / Real.log (N : ℝ) - empiricalA N a cuts hn a s

def empiricalExpression {k n L : ℕ} (N a : ℕ) (cuts : Cuts k n L) (hn : 0 < n)
    (θ : ℝ) (s u : ℕ) : ℝ :=
  (θ + 3) / 2 * empiricalBeta N a cuts hn s - empiricalB N a cuts hn θ s u -
    2 * empiricalB N a cuts hn 2 u (a+L)

/-- Real interval infimum; zero pile sizes are allowed. -/
def empiricalInf {k n L : ℕ} (N a : ℕ) (cuts : Cuts k n L) (hn : 0 < n)
    (s u : ℕ) : ℝ :=
  sInf ((fun θ => empiricalExpression N a cuts hn θ s u) '' Icc 3 4)

def EmpiricalNegativeMargin {k n L : ℕ} (N a : ℕ) (cuts : Cuts k n L)
    (hn : 0 < n) (η : ℝ) : Prop :=
  empiricalBeta N a cuts hn (a+L) ≤ -η ∧
  ∀ s u : ℕ, a ≤ s → s ≤ u → u ≤ a+L → empiricalInf N a cuts hn s u ≤ -η

def FirstColumnGood {k n L : ℕ} (cuts : Cuts k n L) (hn : 0 < n) (g : ℝ) : Prop :=
  ∃ hL : 0 < L, GoodColumn (cuts.profile hn ⟨0, hL⟩) g

/-- Literal manuscript local condition for the original whole deck and its clock. -/
abbrev LocalGood := @TimeProfile.LocalGood

end RiffleUpperV2
