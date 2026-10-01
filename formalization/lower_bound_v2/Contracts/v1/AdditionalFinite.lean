import Contracts.v1.Ascent
import Contracts.v1.Endpoints

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Targets
open TimeProfile

/-- LB01; permutation of labels in every column leaves the actual matrix law invariant. -/
def RowRelabeling : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K) (σ : Permutation N),
    (fixedCountPMF cuts).map (fun ω i => sampleRow ω (σ i)) = (fixedCountPMF cuts).map sampleRow

def StableTie : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K) (ω : Sample cuts) (i j : Fin N),
    i < j → sortedWord ω i = sortedWord ω j → stableSort ω i < stableSort ω j

def PrefixRanks : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K) (ω : Sample cuts) (w : Prefix k K),
    (∀ i : Fin N, (sortedWord ω i).toList.take w.1.val = w.2.toList ↔
      lowerRank w ω ≤ i.val ∧ i.val < upperRank w ω) ∧
    upperRank w ω - lowerRank w ω = prefixCount w ω

/-- LB02: all positive power parameters, including s>1. -/
def HypergeometricTransform : Prop :=
  ∀ M x m : ℕ, 0 < M → x ≤ M → m ≤ M → ∀ s : ℝ, 0 < s →
    expect (uniformPermutation M)
      (fun σ => s ^ (Finset.univ.filter (fun i : Fin M => i.val < x ∧ (σ.symm i).val < m)).card) ≤
      (1 - (m : ℝ)/M + (m : ℝ)/M*s)^x

/-- LB03: residual moments are proved directly; this lane does not depend on LB02. -/
def ResidualJointFactorial : Prop :=
  ∀ {k N K b d : ℕ} (cuts : Cuts k N K) (p : RowPrescription N k K b),
    b < N → Function.Injective p.row →
    0 < probability (fixedCountPMF cuts) (prescriptionEvent p) →
    ∀ (w : Fin d → Word k K) (r : Fin d → ℕ), Function.Injective w → (∑ i, r i) ≤ N-b →
    conditionalExpect (fixedCountPMF cuts)
      (fun ω => ∏ i, falling (wordCount (w i) ω -
        (Finset.univ.filter (fun q => p.word q = w i)).card) (r i)) (prescriptionEvent p) =
      falling (N-b) (∑ i, r i) *
      ∏ j, ((∏ a, falling (cuts.count j a - usedCount p j a) (requestedCount w r j a)) /
        falling (N-b) (∑ i, r i))

/-- LB04: product law of relative orders on disjoint deterministic position sets. -/
def RelativeOrderIndependence : Prop :=
  ∀ (N d : ℕ) (A : Fin d → Finset (Fin N)),
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) → ∀ τ : Fin d → Permutation N,
    probability (uniformPermutation N)
      (fun π => ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, (π x < π y ↔ τ i x < τ i y)) =
      ∏ i, 1 / ((A i).card.factorial : ℝ)

def BoundaryAscentProbability : Prop :=
  ∀ (N : ℕ) (A B : Finset (Fin N)), Disjoint A B →
    probability (uniformPermutation N) (fun π => ∀ x ∈ A, ∀ y ∈ B, π x < π y) =
      1 / (((A.card+B.card).choose A.card : ℕ) : ℝ)

def BernoulliMGF : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (P : PMF Ω) (A : Ω → Prop) (t : ℝ),
    expect P (fun ω => Real.exp (t * ((if A ω then 1 else 0) - probability P A))) ≤
      Real.exp (t^2/8)

def LeastSuccessfulTranslate : Prop :=
  ∀ (N : ℕ) (H0 : Finset ℤ) (G : PathEdges N) (r : ℝ),
    (∃ q : Fin (N+1), r ≤ ((G ∩ internalEdges (clipTranslate N H0 q.val)).card : ℝ)) →
    ∃ q : Fin (N+1), r ≤ ((G ∩ internalEdges (clipTranslate N H0 q.val)).card : ℝ) ∧
      ∀ q' : Fin (N+1), q' < q → ((G ∩ internalEdges (clipTranslate N H0 q'.val)).card : ℝ) < r

/-- LB10 source prop:largest-prefix, including exact factorial/run factor. -/
def FiniteLargestWordTV : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) (m : ℕ),
    2 ≤ m → m ≤ N → (m : ℝ) ≤ maximalMean cuts hN / 2 →
    1 - Real.exp (-chernoffConstant * maximalMean cuts hN) -
      ((N-m+1 : ℕ) : ℝ)/(m.factorial : ℝ) ≤ tv (physicalInverseLaw cuts) (uniformPermutation N)

end RiffleLowerV2.Targets
