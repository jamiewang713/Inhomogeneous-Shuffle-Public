import RiffleLowerV2.Shared.Smoke
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2
open TimeProfile

abbrev Word := RiffleShuffle.Word
abbrev Prefix := RiffleShuffle.RawPrefix
abbrev Permutation (N : ℕ) := Equiv.Perm (Fin N)
abbrev Sample {k N K : ℕ} (cuts : Cuts k N K) := ShuffleSample cuts

/-- Real finite expectation; probability laws themselves retain PMF normalization. -/
def expect {Ω : Type*} [Fintype Ω] (P : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, (P ω).toReal * f ω

def probability {Ω : Type*} [Fintype Ω] (P : PMF Ω) (A : Ω → Prop) : ℝ :=
  expect P (fun ω => if A ω then 1 else 0)

def variance {Ω : Type*} [Fintype Ω] (P : PMF Ω) (f : Ω → ℝ) : ℝ :=
  expect P (fun ω => (f ω - expect P f) ^ 2)

def tv {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) : ℝ :=
  (∑ ω, |(P ω).toReal - (Q ω).toReal|) / 2

def uniformPermutation (N : ℕ) : PMF (Permutation N) := PMF.uniformOfFintype _

def rowWord {k N K : ℕ} {cuts : Cuts k N K} (ω : Sample cuts) (i : Fin N) : Word k K :=
  List.Vector.ofFn (sampleRow ω i)

def stableSort {k N K : ℕ} {cuts : Cuts k N K} (ω : Sample cuts) : Permutation N :=
  Tuple.sort (rowWord ω)

def sortedWord {k N K : ℕ} {cuts : Cuts k N K} (ω : Sample cuts) (i : Fin N) : Word k K :=
  rowWord ω (stableSort ω i)

/-- Actual stable full-word sorting pushforward; sorted position → original label. -/
def matrixLaw {k N K : ℕ} (cuts : Cuts k N K) : PMF (Permutation N) :=
  (fixedCountPMF cuts).map stableSort

/-- A column is the interleaving's pile-label word on its output positions. -/
def oneStepForward {k N K : ℕ} {cuts : Cuts k N K}
    (j : Fin K) (a : ColumnAssignments cuts j) : Permutation N :=
  (Tuple.sort a.val).symm

/-- Decks are position→label. Update D to D ∘ τ_j, for j=0,1,…,K−1. -/
def physicalForward {k N K : ℕ} {cuts : Cuts k N K} (ω : Sample cuts) : Permutation N :=
  (List.finRange K).foldl (fun deck j => (oneStepForward j (ω j)).trans deck) (Equiv.refl _)

def physicalInverse {k N K : ℕ} {cuts : Cuts k N K} (ω : Sample cuts) : Permutation N :=
  (physicalForward ω).symm

def physicalForwardLaw {k N K : ℕ} (cuts : Cuts k N K) : PMF (Permutation N) :=
  (fixedCountPMF cuts).map physicalForward

def physicalInverseLaw {k N K : ℕ} (cuts : Cuts k N K) : PMF (Permutation N) :=
  (fixedCountPMF cuts).map physicalInverse

def prefixMass {k N K : ℕ} (cuts : Cuts k N K) (w : Prefix k K) : ℝ :=
  ∏ j : Fin w.1.val, (cuts.count ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ w.1.isLt)⟩
    (w.2.get j) : ℝ) / N

def prefixCount {k N K : ℕ} {cuts : Cuts k N K} (w : Prefix k K) (ω : Sample cuts) : ℕ :=
  (Finset.univ.filter fun i => (rowWord ω i).toList.take w.1.val = w.2.toList).card

def lowerRank {k N K : ℕ} {cuts : Cuts k N K} (w : Prefix k K) (ω : Sample cuts) : ℕ :=
  (Finset.univ.filter fun i => (rowWord ω i).toList.take w.1.val < w.2.toList).card

def upperRank {k N K : ℕ} {cuts : Cuts k N K} (w : Prefix k K) (ω : Sample cuts) : ℕ :=
  (Finset.univ.filter fun i => (rowWord ω i).toList.take w.1.val ≤ w.2.toList).card

def prefixMean {k N K : ℕ} (cuts : Cuts k N K) (w : Prefix k K) : ℝ :=
  N * prefixMass cuts w

def fullPrefix {k K : ℕ} (w : Word k K) : Prefix k K := ⟨Fin.last K, w⟩
def wordMass {k N K : ℕ} (cuts : Cuts k N K) (w : Word k K) : ℝ := prefixMass cuts (fullPrefix w)
def wordCount {k N K : ℕ} {cuts : Cuts k N K} (w : Word k K) (ω : Sample cuts) : ℕ :=
  prefixCount (fullPrefix w) ω

def toPileProfile {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) (hk : 2 ≤ k) :
    RiffleShuffle.PileProfile N k K := ⟨cuts.count, hN, hk, cuts.sum_count⟩

def toMatrix {k N K : ℕ} {cuts : Cuts k N K} (hN : 0 < N) (hk : 2 ≤ k)
    (ω : Sample cuts) : RiffleShuffle.ShuffleMatrix (toPileProfile cuts hN hk) :=
  ⟨rowWord ω, by intro j a; simpa [rowWord, toPileProfile, sampleRow] using sample_column_counts ω j a⟩

@[simp] theorem rowWord_get {k N K : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) (i : Fin N) (j : Fin K) : (rowWord ω i).get j = sampleEntry ω i j := by
  simp [rowWord, sampleRow]

@[simp] theorem toMatrix_sort {k N K : ℕ} {cuts : Cuts k N K}
    (hN : 0 < N) (hk : 2 ≤ k) (ω : Sample cuts) : (toMatrix hN hk ω).sortPerm = stableSort ω := rfl

/-- This definitional inversion bridge is distinct from the pending matrix-law bridge. -/
theorem physicalInverseLaw_eq_map {k N K : ℕ} (cuts : Cuts k N K) :
    physicalInverseLaw cuts = (physicalForwardLaw cuts).map Equiv.symm := by
  rw [physicalForwardLaw, PMF.map_comp]
  rfl

end RiffleLowerV2
