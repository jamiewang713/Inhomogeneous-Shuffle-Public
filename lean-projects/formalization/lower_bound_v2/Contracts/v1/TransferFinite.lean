import Contracts.v1.AdditionalFinite

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped BigOperators
namespace RiffleLowerV2.Targets
open TimeProfile

/-- LB07: spatial continuity, and scalar integrability for this observable, are explicit. -/
def GenericQuadrature : Prop :=
  ∀ (k N : ℕ) (hN : 2 ≤ N) (T rho phi omega M : ℝ),
    0 < T → 0 < rho → 0 ≤ phi → 0 ≤ omega → 0 ≤ M →
    ∀ (P : BorelPartition k) (μ : TimeLaw k) (f : Simplex k → ℝ),
      Continuous f → (∀ p, 0 ≤ f p ∧ f p ≤ M) →
      (∀ i p q, P.classify p = i → P.classify q = i → |f p - f q| ≤ omega) →
      (∀ i, IntervalIntegrable (cellMass μ P i) volume 0 T) →
      IntervalIntegrable (fun t => ∫ p, f p ∂(μ t : Measure (Simplex k))) volume 0 T →
      ∀ cuts : HorizonCuts k N T,
        AlmostLike cuts (deckPos hN) μ P T rho phi →
        ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ horizon N (horizonDepth N T) →
        |empiricalIntegral N (fun j => f (cuts.profile (deckPos hN) j)) r s -
          ∫ t in r..s, ∫ p, f p ∂(μ t : Measure (Simplex k))| ≤
          2*T*omega + M*P.cellCount*phi*T + 4*M*rho +
            (4*M*P.cellCount*(T/rho+2)+6*M)/logScale N

def JointPsiContinuity : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ContinuousOn (fun z : Simplex k × ℝ => psi z.1 z.2) (univ ×ˢ Icc (2 : ℝ) 4)

/-- Numerical residual mean; it is identified with a conditional expectation by LB03. -/
def residualWordMean {k N K b : ℕ} (cuts : Cuts k N K) (p : RowPrescription N k K b)
    (w : Word k K) : ℝ :=
  (N-b : ℕ) * ∏ j, (((cuts.count j (w.get j) - usedCount p j (w.get j) : ℕ) : ℝ) / (N-b : ℕ))

def ResidualRelativeFactorial : Prop :=
  ∀ c C : ℝ, 0 < c → 0 < C → ∀ b0 : ℕ,
  ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, b0 < N0 ∧ 2 ≤ N0 ∧
  ∀ N ≥ N0, ∀ k K b d : ℕ, b ≤ b0 → (K : ℝ) ≤ C*logScale N →
  ∀ (cuts : Cuts k N K) (p : RowPrescription N k K b), Function.Injective p.row →
  0 < probability (fixedCountPMF cuts) (prescriptionEvent p) →
  ∀ (w : Fin d → Word k K) (r : Fin d → ℕ), Function.Injective w →
  (∀ i j, c*N ≤ (cuts.count j ((w i).get j) : ℝ)) →
  ((∑ i, r i) : ℝ) ≤ (N : ℝ)^(1/5 : ℝ) →
    |conditionalExpect (fixedCountPMF cuts)
      (fun ω => ∏ i, falling (wordCount (w i) ω -
        (Finset.univ.filter (fun q => p.word q = w i)).card) (r i)) (prescriptionEvent p) -
      ∏ i, (residualWordMean cuts p (w i))^(r i)| ≤
      D*(K+1)*((∑ i, r i) : ℝ)^2/N * ∏ i, (residualWordMean cuts p (w i))^(r i)

def ResidualMeanComparison : Prop :=
  ∀ c C : ℝ, 0 < c → 0 < C → ∀ b0 : ℕ,
  ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, b0 < N0 ∧ 2 ≤ N0 ∧
  ∀ N ≥ N0, ∀ k K b : ℕ, b ≤ b0 → (K : ℝ) ≤ C*logScale N →
  ∀ (cuts : Cuts k N K) (p : RowPrescription N k K b) (w : Word k K),
  Function.Injective p.row → 0 < probability (fixedCountPMF cuts) (prescriptionEvent p) →
  (∀ j, c*N ≤ (cuts.count j (w.get j) : ℝ)) →
  |residualWordMean cuts p w - (N : ℝ)*wordMass cuts w| ≤
    D*(K+1)*b/N * ((N : ℝ)*wordMass cuts w)

/-- LB08; the deleted-row statistic, including prescriptions containing the tested word. -/
def ConditionalCollisionStability : Prop :=
  ∀ c C : ℝ, 0 < c → 0 < C → ∀ b0 : ℕ,
  ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, b0 < N0 ∧ 2 ≤ N0 ∧
  ∀ N ≥ N0, ∀ k K b : ℕ, b ≤ b0 → (K : ℝ) ≤ C*logScale N →
  ∀ (cuts : Cuts k N K) (p : RowPrescription N k K b) (w : Word k K),
  Function.Injective p.row → 0 < probability (fixedCountPMF cuts) (prescriptionEvent p) →
  (∀ j, c*N ≤ (cuts.count j (w.get j) : ℝ)) →
  |conditionalProbability (fixedCountPMF cuts)
    (fun ω => 2 ≤ wordCount w ω - (Finset.univ.filter (fun q => p.word q = w)).card)
    (prescriptionEvent p) - poissonCollision ((N : ℝ)*wordMass cuts w)| ≤
    D*(N : ℝ)^(-1/100 : ℝ)*poissonCollision ((N : ℝ)*wordMass cuts w)

end RiffleLowerV2.Targets
