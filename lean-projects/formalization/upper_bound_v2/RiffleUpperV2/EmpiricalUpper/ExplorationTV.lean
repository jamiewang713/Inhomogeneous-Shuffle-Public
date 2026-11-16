import RiffleUpperV2.Exponential.Main
import RiffleUpperV2.Exploration.PairHistories
import RiffleUpperV2.Exploration.CoverageCount
import RiffleUpperV2.Exploration.SmallPiles

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.EmpiricalUpper
open Exploration Exponential

/-- Exactly two directions for each initial pile, including empty and tiny piles. -/
def processIndex (k : ℕ) : Fin (2*k) ≃ Fin k × Direction :=
  Fintype.equivOfCardEq (by simp [Nat.mul_comm])

def PairHistoryType {k N L : ℕ} (cuts : Cuts k N (L+1)) (p : Fin k) :=
  (Fin (pileSize cuts p) → Option (Word k (L+1))) ×
    (Fin (pileSize cuts p) → Option (Word k (L+1)))

instance {k N L : ℕ} (cuts : Cuts k N (L+1)) (p : Fin k) :
    Fintype (PairHistoryType cuts p) := inferInstanceAs (Fintype (_ × _))

/-- Concrete finite exploration assembly. Only the concentration and conditional
estimates supplied by C remain as analytic inputs; all histories, increments,
terminal guards, small piles, boundary edges, and the product event are actual. -/
theorem concreteExplorationTV {k N L : ℕ} (cuts : Cuts k N (L+1))
    (hk : 1 ≤ k) (hN : 2 ≤ N) (D B : ℕ) (hB : 2 ≤ B)
    (g ξ η A r γ : ℝ) (hg : 0 < g) (hr : 0 < r) (hγ : 0 ≤ γ)
    (hc : retainedGoodCluster cuts (by omega) D g)
    (hmean : RiffleLowerV2.maximalMean cuts (by omega) ≤ (N : ℝ)^(-η))
    (hexp : A+1 ≤ η*B)
    (hH : probability (fixedCountPMF cuts) (fun ω => ¬ concentrationEvent cuts D g ξ ω) ≤ r)
    (htail : ∀ (p : Fin k) (d : Direction), (N : ℝ)^ξ ≤ (pileSize cuts p : ℝ) →
      ∀ i : ℕ, i ≤ pileSize cuts p → ∀ ω : Sample cuts × Sample cuts,
      0 < probability (independentPairLaw cuts)
        (fun v => pairHistory cuts p d i v = pairHistory cuts p d i ω) →
      pairHistoryGood cuts D g ξ (Real.sqrt r) p d i ω →
      conditionalExpect (independentPairLaw cuts)
        (fun v => (remainingDirectionalCount cuts D g ξ p d i v.1 v.2 : ℝ))
        (fun v => pairHistory cuts p d i v = pairHistory cuts p d i ω) ≤ γ)
    (hsmall : ((componentConstant B)^(2*k)-1)*γ ≤ 1/2) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      Real.sqrt (2*((componentConstant B)^(2*k)-1)*γ)/2 +
      (r+2*N*Real.sqrt r+(k : ℝ)/2*(N : ℝ)^(ξ-η)) +
      (N : ℝ)^(-A)/(B+1).factorial := by
  let e := processIndex k
  let H : Fin (2*k) → Type := fun a => PairHistoryType cuts (e a).1
  let h : ∀ a, ℕ → (Sample cuts × Sample cuts) → H a :=
    fun a => pairHistory cuts (e a).1 (e a).2
  let X : Fin (2*k) → ℕ → (Sample cuts × Sample cuts) → ℕ :=
    fun a i ω => directionalProcess cuts D g ξ (e a).1 (e a).2 i ω.1 ω.2
  let G : Fin (2*k) → ℕ → (Sample cuts × Sample cuts) → Prop :=
    fun a => pairHistoryGood cuts D g ξ (Real.sqrt r) (e a).1 (e a).2
  let m : Fin (2*k) → ℕ := fun a => pileSize cuts (e a).1
  let R := regularityEvent cuts D g ξ (Real.sqrt r)
  have href : ∀ a, Refining (h a) (m a) := by
    intro a i j hij hj ω v hv
    exact pairHistory_refinement cuts _ _ hij hv
  have hunit : ∀ a ω, UnitIncrements (fun i => X a i ω) (m a) := by
    intro a ω i hi
    exact Exploration.unitIncrements cuts D g ξ _ _ i ω.1 ω.2
  have hzero : ∀ a ω, X a 0 ω = 0 := by
    intro a ω
    exact directionalProcess_zero cuts D g ξ _ _ ω.1 ω.2
  have had : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (X a i) := by
    intro a i hi ω v hv
    exact directionalProcess_adapted cuts D g ξ _ _ i hv
  have hG : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (G a i) := by
    intro a i hi ω v hv
    exact propext (pairHistoryGood_adapted cuts D g ξ (Real.sqrt r) _ _ i hv)
  have ht : ∀ a i, i < m a → ∀ v, G a i v →
      0 < probability (independentPairLaw cuts) (fun ω => h a i ω = h a i v) →
      conditionalExpect (independentPairLaw cuts)
        (fun ω => (X a (m a) ω-X a i ω : ℕ)) (fun ω => h a i ω = h a i v) ≤ γ := by
    intro a i hi v hv hp
    by_cases hl : (N : ℝ)^ξ ≤ (pileSize cuts (e a).1 : ℝ)
    · exact htail _ _ hl i (Nat.le_of_lt hi) v hp hv
    · have hz : conditionalExpect (independentPairLaw cuts)
          (fun ω => (X a (m a) ω-X a i ω : ℕ)) (fun ω => h a i ω = h a i v) = 0 := by
        apply conditionalExpect_zero_on
        intro ω hω
        simp [X,directionalProcess,hl]
      exact hz ▸ hγ
  have hC : ∀ ω : Sample cuts × Sample cuts,
      regularTruncation cuts R B ω.1 ∧ regularTruncation cuts R B ω.2 →
      ∀ a, goodPrefix (G a) (m a) ω := by
    intro ω hω a i hi
    exact regularity_pairHistoryGood cuts D g ξ (Real.sqrt r) _ _ i hω.1.1 hω.2.1
  have hcover : ∀ ω : Sample cuts × Sample cuts,
      regularTruncation cuts R B ω.1 ∧ regularTruncation cuts R B ω.2 →
      (shuffleEdges ω.1 ∩ shuffleEdges ω.2).card ≤ ∑ a, X a (m a) ω := by
    intro ω hω
    have hh := sharedEdges_le_directionalProcesses cuts (by omega) hk D hg hc hω.1.1 hω.2.1
    have he := e.sum_comp (fun a : Fin k × Direction =>
      directionalProcess cuts D g ξ a.1 a.2 (pileSize cuts a.1) ω.1 ω.2)
    rw [Fintype.sum_prod_type] at he
    exact hh.trans_eq he.symm
  have htv := boundedComponentExplorationTV cuts hN R B hB hmean hexp
    (2*k) (by omega) H h X G m γ hγ href hunit hzero had hG ht hC hcover hsmall
  have hreg := regularityFailure_of_bounds cuts D g ξ r
    ((k : ℝ)/2*(N : ℝ)^(ξ-η)) hr hH (smallPileFailure cuts hN ξ η hmean)
  exact htv.trans (by dsimp [R] at *; linarith)

end RiffleUpperV2.EmpiricalUpper
