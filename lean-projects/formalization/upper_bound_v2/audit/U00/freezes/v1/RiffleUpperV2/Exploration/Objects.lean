import RiffleUpperV2.Shared.Empirical
import RiffleLowerV2.Shared.Statistics

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exploration
open TimeProfile

inductive Direction where
  | forward | backward
  deriving DecidableEq

instance : Fintype Direction where
  elems := {.forward, .backward}
  complete d := by cases d <;> simp

def windowLength (N : ℕ) (ρ : ℝ) : ℕ := ⌈ρ * Real.log (N : ℝ)⌉₊ + 1

def clusterSpan (γ : ℝ) : ℕ := ⌈6 / γ⌉₊

/-- Integer-window form of local goodness, with the endpoint-column loss retained. -/
def integerWindowGood {k n L : ℕ} (N : ℕ) (cuts : Cuts k n (L+1))
    (hn : 0 < n) (ρ γ g : ℝ) : Prop :=
  ∀ b : ℕ, b + windowLength N ρ ≤ L+1 →
    γ * ρ * Real.log (N : ℝ) - 2 ≤
      ((Finset.univ.filter fun j : Fin (L+1) => b ≤ j.val ∧
        j.val < b + windowLength N ρ ∧ GoodColumn (cuts.profile hn j) g).card : ℝ)

/-- The retained first column and two later good columns in the chosen short span. -/
def retainedGoodCluster {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (D : ℕ) (g : ℝ) : Prop :=
  GoodColumn (cuts.profile hn 0) g ∧
    ∃ j₁ j₂ : Fin (L+1), 0 < j₁.val ∧ j₁ < j₂ ∧ j₂.val ≤ D ∧
      GoodColumn (cuts.profile hn j₁) g ∧ GoodColumn (cuts.profile hn j₂) g

/-- Zero-based starting position of a first-column pile. Manuscript o_p is this plus one. -/
def pileOffset {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) : ℕ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin k => q < p), cuts.count 0 q

def pileSize {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) : ℕ := cuts.count 0 p

theorem pileOffset_add_size_le {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) :
    pileOffset cuts p + pileSize cuts p ≤ n := by
  have he : pileOffset cuts p + pileSize cuts p =
      ∑ q ∈ insert p (Finset.univ.filter (fun q : Fin k => q < p)), cuts.count 0 q := by
    rw [Finset.sum_insert (by simp)]
    simp only [pileOffset, pileSize]
    omega
  rw [he]
  exact (Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)).trans_eq (cuts.sum_count 0)

/-- Spatial reversal leaves the order of word coordinates unchanged. -/
def spatialIndex {m : ℕ} (d : Direction) (r : Fin m) : Fin m :=
  match d with
  | .forward => r
  | .backward => ⟨m - 1 - r.val, by omega⟩

def pilePosition {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (r : Fin (pileSize cuts p)) : Fin n :=
  ⟨pileOffset cuts p + (spatialIndex d r).val,
    lt_of_lt_of_le (Nat.add_lt_add_left (spatialIndex d r).isLt _)
      (pileOffset_add_size_le cuts p)⟩

/-- A finite tuple containing precisely this pile's first i spatially revealed words.
The unrevealed coordinates are None, a deterministic padding. -/
def naturalHistory {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (i : ℕ) (ω : Sample cuts) :
    Fin (pileSize cuts p) → Option (Word k (L+1)) :=
  fun r => if r.val < i then some (sortedWord ω (pilePosition cuts p d r)) else none

def historyFiber {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (i : ℕ) (ω : Sample cuts) : Sample cuts → Prop :=
  fun v => naturalHistory cuts p d i v = naturalHistory cuts p d i ω

def positiveHistory {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (i : ℕ) (ω : Sample cuts) : Prop :=
  0 < probability (fixedCountPMF cuts) (historyFiber cuts p d i ω)

/-- A short tail prefix omits the first-column pile digit. -/
def tailPrefix {k L : ℕ} (D : ℕ) (w : Word k (L+1)) : Word k (min D L) :=
  List.Vector.ofFn fun r => w.get ⟨r.val+1, by have := r.isLt; omega⟩

def tailMass {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ)
    (v : Word k (min D L)) : ℝ :=
  ∏ r : Fin (min D L), (cuts.count ⟨r.val+1, by have := r.isLt; omega⟩ (v.get r) : ℝ) / n

def reserveMass (k D : ℕ) (g : ℝ) : ℝ := g^2 * (k : ℝ)^(-(D : ℝ))

/-- Finite deterministic candidate set; existence is a separate good-cluster obligation. -/
def reserveCandidates {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ) :
    Finset (Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L)) :=
  Finset.univ.filter fun v => v.1 < v.2.1 ∧ v.2.1 < v.2.2 ∧
    reserveMass k D g ≤ tailMass cuts D v.1 ∧
    reserveMass k D g ≤ tailMass cuts D v.2.1 ∧
    reserveMass k D g ≤ tailMass cuts D v.2.2

/-- Selection depends only on cuts; an absent cluster is represented by None. -/
def chosenReserves {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ) :
    Option (Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L)) :=
  if h : (reserveCandidates cuts D g).Nonempty then
    some ((reserveCandidates cuts D g).min' h) else none

def hasDirection {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (d : Direction) (w : Word k (L+1)) : Prop :=
  match chosenReserves cuts D g with
  | none => False
  | some v => match d with
    | .forward => tailPrefix D w ≤ v.2.1
    | .backward => v.2.1 ≤ tailPrefix D w

def beforeMiddle {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (w : Word k (L+1)) : Prop :=
  ∃ v, chosenReserves cuts D g = some v ∧ tailPrefix D w < v.2.1

def throughMiddle {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (w : Word k (L+1)) : Prop :=
  ∃ v, chosenReserves cuts D g = some v ∧ tailPrefix D w ≤ v.2.1

def guardCount {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (p : Fin k) (through : Bool) (ω : Sample cuts) : ℕ :=
  (Finset.univ.filter fun r : Fin n =>
    (rowWord ω r).get 0 = p ∧
      if through then throughMiddle cuts D g (rowWord ω r)
      else beforeMiddle cuts D g (rowWord ω r)).card

def guardMean {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (p : Fin k) (through : Bool) : ℝ :=
  expect (fixedCountPMF cuts) (fun ω => (guardCount cuts D g p through ω : ℝ))

def outsideCount {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (j : Fin (L+1)) (a : Fin k) (ω : Sample cuts) : ℕ :=
  (Finset.univ.filter fun r : Fin n => (rowWord ω r).get 0 ≠ p ∧
    (rowWord ω r).get j = a).card

def prefixLaterCount {k n L : ℕ} (cuts : Cuts k n (L+1))
    (x : Prefix k (L+1)) (j : Fin (L+1)) (a : Fin k) (ω : Sample cuts) : ℕ :=
  (Finset.univ.filter fun r : Fin n =>
    (rowWord ω r).toList.take x.1.val = x.2.toList ∧ (rowWord ω r).get j = a).card

/-- Literal one-matrix simultaneous concentration event; independent of all histories. -/
def concentrationEvent {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g ξ : ℝ)
    (ω : Sample cuts) : Prop :=
  (∀ p j a, 0 < j.val →
    |(outsideCount cuts p j a ω : ℝ) - (n - pileSize cuts p : ℕ) *
      ((cuts.count j a : ℝ) / n)| ≤ (n : ℝ)^((2:ℝ)/3)) ∧
  (∀ x : Prefix k (L+1), (n : ℝ)^ξ ≤ prefixMean cuts x →
    |(prefixCount x ω : ℝ) - prefixMean cuts x| ≤ (prefixMean cuts x)^((2:ℝ)/3) ∧
    ∀ j a, x.1.val ≤ j.val →
      |(prefixLaterCount cuts x j a ω : ℝ) - (prefixCount x ω : ℝ) *
        ((cuts.count j a : ℝ) / n)| ≤ (prefixMean cuts x)^((2:ℝ)/3)) ∧
  (∀ p, (n : ℝ)^ξ ≤ (pileSize cuts p : ℝ) → ∀ through : Bool,
    |(guardCount cuts D g p through ω : ℝ) - guardMean cuts D g p through| ≤
      reserveMass k D g * pileSize cuts p / 4)

def badBound (n : ℕ) (ξ A c : ℝ) : ℝ :=
  A * (n : ℝ)^A * Real.exp (-c * (n : ℝ)^(ξ/3))

def historyGood {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g ξ ε : ℝ)
    (p : Fin k) (d : Direction) (i : ℕ) (ω : Sample cuts) : Prop :=
  RiffleLowerV2.conditionalProbability (fixedCountPMF cuts)
    (fun v => ¬ concentrationEvent cuts D g ξ v) (historyFiber cuts p d i ω) ≤ ε

/-- Directional edge indexed by its position in reveal order. -/
def directionalEdge {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (p : Fin k) (d : Direction) (e : Fin (pileSize cuts p - 1))
    (ω : Sample cuts) : Prop :=
  let u : Fin (pileSize cuts p) := ⟨e.val, by omega⟩
  let v : Fin (pileSize cuts p) := ⟨e.val+1, by omega⟩
  sortedWord ω (pilePosition cuts p d u) = sortedWord ω (pilePosition cuts p d v) ∧
    hasDirection cuts D g d (sortedWord ω (pilePosition cuts p d u))

/-- Unused small/empty piles are identically zero. There are exactly 2k indices (p,d). -/
def directionalProcess {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g ξ : ℝ)
    (p : Fin k) (d : Direction) (i : ℕ) (ω ω' : Sample cuts) : ℕ :=
  if (n : ℝ)^ξ ≤ (pileSize cuts p : ℝ) then
    (Finset.univ.filter fun e : Fin (pileSize cuts p - 1) => e.val+1 < i ∧
      directionalEdge cuts D g p d e ω ∧ directionalEdge cuts D g p d e ω').card
  else 0

/-- e+1 ≥ i retains the crossing edge e=i-1 at time i. -/
def remainingDirectionalCount {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g ξ : ℝ)
    (p : Fin k) (d : Direction) (i : ℕ) (ω ω' : Sample cuts) : ℕ :=
  directionalProcess cuts D g ξ p d (pileSize cuts p) ω ω' -
    directionalProcess cuts D g ξ p d i ω ω'

def pairHistory {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (d : Direction)
    (i : ℕ) (ω : Sample cuts × Sample cuts) :=
  (naturalHistory cuts p d i ω.1, naturalHistory cuts p d i ω.2)

def pairHistoryGood {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g ξ ε : ℝ)
    (p : Fin k) (d : Direction) (i : ℕ) (ω : Sample cuts × Sample cuts) : Prop :=
  if i = 0 ∨ pileSize cuts p ≤ i then True else
    historyGood cuts D g ξ ε p d i ω.1 ∧ historyGood cuts D g ξ ε p d i ω.2

def pileEdgeFree {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) : Prop :=
  ∀ e : Fin (pileSize cuts p - 1),
    sortedWord ω (pilePosition cuts p .forward ⟨e.val, by omega⟩) ≠
      sortedWord ω (pilePosition cuts p .forward ⟨e.val+1, by omega⟩)

def regularityEvent {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g ξ ε : ℝ)
    (ω : Sample cuts) : Prop :=
  concentrationEvent cuts D g ξ ω ∧
  (∀ p d i, 0 < i → i < pileSize cuts p → historyGood cuts D g ξ ε p d i ω) ∧
  (∀ p, (pileSize cuts p : ℝ) < (n : ℝ)^ξ → pileEdgeFree cuts p ω)

end RiffleUpperV2.Exploration
