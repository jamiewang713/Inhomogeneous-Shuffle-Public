import RiffleLowerV2.Shared.Statistics

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Targets
open TimeProfile

/-- LB01: independent columns, as an unconditional product-expectation identity. -/
def ColumnIndependence : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K) (f : ∀ j, ColumnAssignments cuts j → ℝ),
    expect (fixedCountPMF cuts) (fun ω => ∏ j, f j (ω j)) =
      ∏ j, expect (columnPMF cuts j) (f j)

/-- LB01: graph sampling followed by an independent uniform permutation. -/
def GraphRepresentation : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K), matrixLaw cuts = graphMixtureLaw cuts

def GraphEventIdentity : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K) (A : Permutation N → Prop),
    probability (matrixLaw cuts) A = expect (fixedCountPMF cuts) (fun ω =>
      probability (uniformPermutation N) (fun π => A (componentSort (shuffleEdges ω) π)))

/-- LB01: chronological physical inverse, not a definition of the matrix law. -/
def PhysicalMatrixBridge : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K), physicalInverseLaw cuts = matrixLaw cuts

def InversionTV : Prop :=
  ∀ (N : ℕ) (P : PMF (Permutation N)),
    tv (P.map Equiv.symm) (uniformPermutation N) = tv P (uniformPermutation N)

/-- Subset model: independent uniform permutations generate initial-segment subsets. -/
def thinningCount {M d : ℕ} (m : Fin d → ℕ) (ω : Fin d → Permutation M) : ℕ :=
  (Finset.univ.filter fun i => ∀ j, ((ω j).symm i).val < m j).card

def thinningQ {d : ℕ} (M : ℕ) (m : Fin d → ℕ) : ℝ := ∏ j, (m j : ℝ) / M

def SuccessiveThinning : Prop :=
  ∀ (M d : ℕ), 0 < M → ∀ (m : Fin d → ℕ), (∀ j, m j ≤ M) →
  ∀ s : ℝ, 0 < s →
    expect (PMF.uniformOfFintype (Fin d → Permutation M)) (fun ω => s ^ thinningCount m ω) ≤
      (1 - thinningQ M m + thinningQ M m * s)^M ∧
    (1 - thinningQ M m + thinningQ M m * s)^M ≤ Real.exp (M * thinningQ M m * (s-1))

def PrefixTails : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K), 0 < N → ∀ w : Prefix k K,
  (∀ t : ℝ, 0 < t →
    probability (fixedCountPMF cuts) (fun ω => t ≤ |(prefixCount w ω : ℝ) - prefixMean cuts w|) ≤
      2 * Real.exp (-t^2 / (4 * (prefixMean cuts w + t)))) ∧
  probability (fixedCountPMF cuts) (fun ω => (prefixCount w ω : ℝ) ≤ prefixMean cuts w / 2) ≤
    Real.exp (-chernoffConstant * prefixMean cuts w) ∧
  probability (fixedCountPMF cuts) (fun ω => prefixCount w ω < 2) ≤
    2 * Real.exp (-prefixMean cuts w / 2)

def AllPrefixConcentration : Prop :=
  ∀ {k N K : ℕ} (cuts : Cuts k N K), 2 ≤ N → ∀ ε : ℝ, 0 < ε →
    probability (fixedCountPMF cuts) (fun ω => ¬allPrefixEvent ε ω) ≤ prefixFailure N k K ε

def PrefixFailureUniform : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T ε δ : ℝ, 0 < T → 0 < ε → 0 < δ →
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ K : ℕ, (K : ℝ) ≤ T * logScale N → prefixFailure N k K ε ≤ δ

/-- LB02: positive-probability prescriptions produce actual residual fixed counts.
An arbitrary bijective enumeration of the unused labels is permitted. -/
def ResidualLaw : Prop :=
  ∀ {k N K b : ℕ} (cuts : Cuts k N K) (r : RowPrescription N k K b),
    b < N → Function.Injective r.row →
    0 < probability (fixedCountPMF cuts) (prescriptionEvent r) →
    ∃ residual : Cuts k (N-b) K,
      (∀ j a, residual.count j a = cuts.count j a - usedCount r j a) ∧
      ∀ e : Fin (N-b) → Fin N, Function.Injective e →
        (∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) →
        ∀ rows : Fin (N-b) → Fin K → Fin k,
          conditionalProbability (fixedCountPMF cuts)
            (fun ω => ∀ q j, sampleEntry ω (e q) j = rows q j) (prescriptionEvent r) =
          (((fixedCountPMF residual).map sampleRow) rows).toReal

end RiffleLowerV2.Targets
