import RiffleLowerV2.Shared.Model

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2

/-- An edge is identified by its zero-based left position. -/
abbrev PathEdges (N : ℕ) := Finset (Fin (N - 1))
def edgeLeft {N : ℕ} (e : Fin (N-1)) : Fin N := ⟨e.val, by omega⟩
def edgeRight {N : ℕ} (e : Fin (N-1)) : Fin N := ⟨e.val+1, by omega⟩
def manuscriptRank {N : ℕ} (i : Fin N) : ℤ := (i.val : ℤ) + 1

def internalEdges {N : ℕ} (H : Finset (Fin N)) : PathEdges N :=
  Finset.univ.filter fun e => edgeLeft e ∈ H ∧ edgeRight e ∈ H

/-- Boundary in the infinite integer path, including endpoints 0/1 and N/N+1. -/
def integerBoundary (H : Finset ℤ) : Finset ℤ :=
  (H ∪ H.image (fun z => z-1)).filter fun z => (z ∈ H ∧ z+1 ∉ H) ∨ (z ∉ H ∧ z+1 ∈ H)

def rankSet {N : ℕ} (H : Finset (Fin N)) : Finset ℤ := H.image manuscriptRank
def boundary {N : ℕ} (H : Finset (Fin N)) : Finset ℤ := integerBoundary (rankSet H)

/-- Literal paper H_q=(q+H0)∩[N], represented on zero-based Lean positions. -/
def clipTranslate (N : ℕ) (H0 : Finset ℤ) (q : ℤ) : Finset (Fin N) :=
  Finset.univ.filter fun i => manuscriptRank i - q ∈ H0

def shuffleEdges {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : Sample cuts) : PathEdges N :=
  Finset.univ.filter fun e => sortedWord ω (edgeLeft e) = sortedWord ω (edgeRight e)

/-- Increasing component number; absent path edges separate components. -/
def componentIndex {N : ℕ} (G : PathEdges N) (i : Fin N) : ℕ :=
  (Finset.univ.filter fun e : Fin (N-1) => e.val < i.val ∧ e ∉ G).card

/-- Sort values within components. Component number is the primary sorting key. -/
def componentSort {N : ℕ} (G : PathEdges N) (π : Permutation N) : Permutation N :=
  (Tuple.sort (fun i => (toLex (componentIndex G i, π i) : ℕ ×ₗ Fin N))).trans π

def graphMixtureLaw {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) : PMF (Permutation N) :=
  (TimeProfile.fixedCountPMF cuts).bind fun ω =>
    (uniformPermutation N).map (componentSort (shuffleEdges ω))

def ascentCount {N : ℕ} (H : Finset (Fin N)) (σ : Permutation N) : ℕ :=
  ((internalEdges H).filter fun e => σ (edgeLeft e) < σ (edgeRight e)).card

def scan {N : ℕ} (H0 : Finset ℤ) (s : ℝ) (σ : Permutation N) : Prop :=
  ∃ q : Fin (N+1), (ascentCount (clipTranslate N H0 q.val) σ : ℝ) >
    ((internalEdges (clipTranslate N H0 q.val)).card : ℝ) / 2 + s

theorem rank_interval_iff {N L U : ℕ} (i : Fin N) :
    L ≤ i.val ∧ i.val < U ↔ (L : ℤ) < manuscriptRank i ∧ manuscriptRank i ≤ (U : ℤ) := by
  simp only [manuscriptRank]
  omega

@[simp] theorem mem_clipTranslate {N : ℕ} (H0 : Finset ℤ) (q : ℤ) (i : Fin N) :
    i ∈ clipTranslate N H0 q ↔ manuscriptRank i - q ∈ H0 := by simp [clipTranslate]

end RiffleLowerV2
