import Contracts.v1.TransferFinite
import Contracts.v1.WitnessGeometry

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Targets
open TimeProfile

/-- LB04: the two-sided form on the same actual component statistic. -/
def ComponentConcentrationTwoSided : Prop :=
  ∀ (N : ℕ) (G : PathEdges N) (H : Finset (Fin N)) (M t : ℝ),
    0 < M → (H.card : ℝ) ≤ M → 0 < t →
    let X := fun π => (ascentCount H (componentSort G π) : ℝ)
    probability (uniformPermutation N)
      (fun π => t ≤ |X π - expect (uniformPermutation N) X|) ≤ 2*Real.exp (-t^2/M)

/-- LB02 exact mean exponent adapter for the canonical maximal full word. -/
def MaximalMeanIdentity : Prop :=
  ∀ k N K : ℕ, 2 ≤ k → ∀ (hN : 2 ≤ N) (cuts : Cuts k N K),
    ∃ w : Word k K, IsCanonicalMaxWord cuts w ∧
      (N : ℝ)*wordMass cuts w = maximalMean cuts (deckPos hN) ∧
      maximalMean cuts (deckPos hN) = (N : ℝ)^(beta cuts (deckPos hN) (horizon N K))

/-- LB08 summed collision-count concentration, uniformly over varying families. -/
def CollisionChebyshev : Prop :=
  ∀ c C : ℝ, 0 < c → 0 < C → ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ,
  ∀ N ≥ N0, ∀ k K : ℕ, (K : ℝ) ≤ C*logScale N →
  ∀ (cuts : Cuts k N K) (W : Finset (Word k K)), selectedPiles cuts W c →
  ∀ t : ℝ, 0 < t → 0 < expect (fixedCountPMF cuts) (collisionCount W) →
  probability (fixedCountPMF cuts) (fun ω =>
    t * expect (fixedCountPMF cuts) (collisionCount W) ≤
      |collisionCount W ω - expect (fixedCountPMF cuts) (collisionCount W)|) ≤
    1 / (t^2 * expect (fixedCountPMF cuts) (collisionCount W)) + D*(N : ℝ)^(-1/100 : ℝ)/t^2

/-- LB10 intermediate output. Geometry is supplied as a previously proved spec;
this is not an extra assumption in either endpoint. -/
def ManyEdgesTarget : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T eta rho chiGood xi : ℝ,
  0 < T → 0 < eta → 0 < rho → 0 < chiGood → 0 < xi →
  ∀ (P : BorelPartition k) (epsilon : ℝ), 0 < epsilon →
  ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
  ∀ (cuts : HorizonCuts k N T) (hN : 0 < N) (W : ColdWitnessData)
    (G : ColdGeometryData (horizonDepth N T) P W),
    WitnessSpec cuts hN eta rho chiGood W → GeometrySpec cuts hN eta rho chiGood xi P W G →
    let Hrel := coldRelativeSet cuts hN P W G
    1-epsilon ≤ probability (fixedCountPMF cuts) (fun ω =>
      (Hrel.card : ℝ)^(1/2+kappa eta/5) ≤
        ((shuffleEdges ω ∩ internalEdges (clipTranslate N Hrel
          (lowerRank (prefixAt W.ms G.ambient) ω : ℤ))).card : ℝ))

end RiffleLowerV2.Targets
