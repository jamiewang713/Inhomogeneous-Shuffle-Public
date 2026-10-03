import RiffleLowerV2.Shared.Empirical
import RiffleLowerV2.Shared.Path

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2
open TimeProfile

def chernoffConstant : ℝ := (1 - Real.log 2) / 2

def allPrefixEvent {k N K : ℕ} {cuts : Cuts k N K} (ε : ℝ) (ω : Sample cuts) : Prop :=
  ∀ w : Prefix k K, |(prefixCount w ω : ℝ) - prefixMean cuts w| ≤
    (N : ℝ)^ε * (Real.sqrt (prefixMean cuts w) + 1)

def prefixFailure (N k K : ℕ) (ε : ℝ) : ℝ :=
  2 * (K+1) * (k : ℝ)^K * Real.exp (-(N : ℝ)^ε / 8)

/-- Only prescribed row indices and digits are data. Admissibility is separate. -/
structure RowPrescription (N k K b : ℕ) where
  row : Fin b → Fin N
  word : Fin b → Word k K

def prescriptionEvent {N k K b : ℕ} {cuts : Cuts k N K} (r : RowPrescription N k K b)
    (ω : Sample cuts) : Prop := ∀ i, rowWord ω (r.row i) = r.word i

def usedCount {N k K b : ℕ} (r : RowPrescription N k K b) (j : Fin K) (a : Fin k) : ℕ :=
  (Finset.univ.filter fun i => (r.word i).get j = a).card

def conditionalProbability {Ω : Type*} [Fintype Ω] (P : PMF Ω) (A B : Ω → Prop) : ℝ :=
  probability P (fun ω => A ω ∧ B ω) / probability P B

def conditionalExpect {Ω : Type*} [Fintype Ω] (P : PMF Ω) (f : Ω → ℝ) (B : Ω → Prop) : ℝ :=
  expect P (fun ω => if B ω then f ω else 0) / probability P B

def falling (n r : ℕ) : ℝ := (n.descFactorial r : ℝ)

def requestedCount {k K d : ℕ} (w : Fin d → Word k K) (r : Fin d → ℕ)
    (j : Fin K) (a : Fin k) : ℕ := ∑ i, if (w i).get j = a then r i else 0

def factorialProduct {N k K d : ℕ} {cuts : Cuts k N K}
    (w : Fin d → Word k K) (r : Fin d → ℕ) (ω : Sample cuts) : ℝ :=
  ∏ i, falling (wordCount (w i) ω) (r i)

def exactFactorial {N k K d : ℕ} (cuts : Cuts k N K)
    (w : Fin d → Word k K) (r : Fin d → ℕ) : ℝ :=
  falling N (∑ i, r i) * ∏ j, ((∏ a, falling (cuts.count j a) (requestedCount w r j a)) /
    falling N (∑ i, r i))

def poissonCollision (t : ℝ) : ℝ := 1 - (1+t) * Real.exp (-t)
def bonferroni (m n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 m, (-1 : ℝ)^r * (r-1 : ℕ) * (n.choose r : ℝ)
def bonferroniRemainder (m n : ℕ) : ℝ := (m-1 : ℕ) * (n.choose m : ℝ)
def poissonRemainder (m : ℕ) (t : ℝ) : ℝ := (m-1 : ℕ) * t^m / (m.factorial : ℝ)

def collisionEvent {N k K : ℕ} {cuts : Cuts k N K} (w : Word k K) (ω : Sample cuts) : Prop :=
  2 ≤ wordCount w ω

def selectedPiles {N k K : ℕ} (cuts : Cuts k N K) (W : Finset (Word k K)) (c : ℝ) : Prop :=
  ∀ w ∈ W, ∀ j, c * N ≤ (cuts.count j (w.get j) : ℝ)

def collisionCount {N k K : ℕ} {cuts : Cuts k N K} (W : Finset (Word k K)) (ω : Sample cuts) : ℝ :=
  ∑ w ∈ W, if collisionEvent w ω then 1 else 0

def maximalMean {N k K : ℕ} (cuts : Cuts k N K) (hN : 0 < N) : ℝ :=
  N * ∏ j, pileMax (cuts.profile hN j)

def HasIncreasingRun {N : ℕ} (σ : Permutation N) (m : ℕ) : Prop :=
  ∃ a : ℕ, a+m ≤ N ∧ ∀ i j : Fin N, a ≤ i.val → j.val < a+m → i < j → σ i < σ j

end RiffleLowerV2
