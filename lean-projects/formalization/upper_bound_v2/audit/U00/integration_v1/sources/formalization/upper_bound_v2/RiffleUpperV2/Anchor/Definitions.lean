import RiffleUpperV2.Shared.Model
import RiffleUpperV2.Hypergeometric.Cylinder

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

/-- All columns here are strictly after the already exposed anchor column. -/
def Reserve {n : ℕ} (R : Finset (Fin n)) (g : ℝ) : Prop :=
  0 < g ∧ g < 1 ∧ (R.card : ℝ) ≤ (1-g) * n

/-- The column corresponding to a zero-based digit of a local prefix. -/
def prefixColumn {k d : ℕ} (x : Prefix k d) (i : Fin x.1.val) : Fin d :=
  ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ x.1.isLt)⟩

def IsPrefix {k d : ℕ} (y x : Prefix k d) : Prop := y.2.toList <+: x.2.toList

def prefixRows {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (ω : Sample cuts) : Finset (Fin n) :=
  R.filter (fun r => (rowWord ω r).toList.take x.1.val = x.2.toList)

def anchoredMean {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) : ℝ := (R.card : ℝ) * prefixMass cuts x

def Legal {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) : Prop := 0 < anchoredMean cuts R x

def lowerEndpoint {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) : ℤ :=
  c₀ + ((R.filter (fun r => (rowWord ω r).toList.take x.1.val < x.2.toList)).card : ℤ)

def upperEndpoint {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) : ℤ :=
  lowerEndpoint c₀ R x ω + ((prefixRows R x ω).card : ℤ)

/-- The known prefix is included in each stored word only for a simpler finite
codomain; these data are exactly the labeled cylinder and its continuations. -/
abbrev InternalHistory (k n d : ℕ) := Fin n → Option (Fin d → Fin k)

def internalHistory {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (ω : Sample cuts) : InternalHistory k n d :=
  fun r => if r ∈ prefixRows R x ω then some (fun j => sampleEntry ω r j) else none

/-- Finite sigma-field refinement: every fine fiber is in a coarse fiber. -/
def Refines {Ω Γ Δ : Type*} (fine : Ω → Γ) (coarse : Ω → Δ) : Prop :=
  ∀ ω ω', fine ω = fine ω' → coarse ω = coarse ω'

/-- The digit probability uses the full n-label sampling population. -/
def digitProbability {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d) (a : Fin k) : ℝ :=
  (cuts.count j a : ℝ) / n

def leftProbability {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d) (a : Fin k) : ℝ :=
  (Hypergeometric.allowedCount cuts j (Finset.univ.filter (· < a)) : ℝ) / n

def rightProbability {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d) (a : Fin k) : ℝ :=
  (Hypergeometric.allowedCount cuts j (Finset.univ.filter (a < ·)) : ℝ) / n

def sidePrefixMass {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (i : Fin x.1.val) : ℝ :=
  ∏ j : Fin i.val, digitProbability cuts (prefixColumn x ⟨j.val, by omega⟩)
    (x.2.get ⟨j.val, by omega⟩)

def leftMean {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) (i : Fin x.1.val) : ℝ :=
  R.card * sidePrefixMass cuts x i * leftProbability cuts (prefixColumn x i) (x.2.get i)

def rightMean {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) (i : Fin x.1.val) : ℝ :=
  R.card * sidePrefixMass cuts x i * rightProbability cuts (prefixColumn x i) (x.2.get i)

/-- A boundary digit is genuine only if it lies strictly after the anchor. -/
def LeftCrossing {k n d : ℕ} (cuts : Cuts k n d) (χ : ℝ) (y : Prefix k d) : Prop :=
  ∃ hy : 0 < y.1.val,
    χ ≤ leftProbability cuts (prefixColumn y ⟨y.1.val-1, by omega⟩)
      (y.2.get ⟨y.1.val-1, by omega⟩)

def RightCrossing {k n d : ℕ} (cuts : Cuts k n d) (χ : ℝ) (z : Prefix k d) : Prop :=
  ∃ hz : 0 < z.1.val,
    χ ≤ rightProbability cuts (prefixColumn z ⟨z.1.val-1, by omega⟩)
      (z.2.get ⟨z.1.val-1, by omega⟩)

/-- This data permits x=v, including an immediate-stop join. Terminal fallback
words are not certified as crossings merely by being terminal. -/
structure GenuineBoundaryPair {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (χ : ℝ) (y z v : Prefix k d) : Prop where
  chi_pos : 0 < χ
  chi_lt_one : χ < 1
  left_prefix : IsPrefix y v
  right_prefix : IsPrefix z v
  join_eq : v = y ∨ v = z
  legal_join : Legal cuts R v
  left_crossing : LeftCrossing cuts χ y
  right_crossing : RightCrossing cuts χ z

/-- The image is finite; adjoining zero totalizes empty prefix definitions. -/
def leftScale {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) : ℝ := (insert 0 (Finset.univ.image (leftMean cuts R v))).sup' (by simp)
    id

def rightScale {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) : ℝ := (insert 0 (Finset.univ.image (rightMean cuts R v))).sup' (by simp)
    id

def sideScale {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) : ℝ := min (leftScale cuts R v) (rightScale cuts R v)

def varianceDenominator {k d : ℕ} (χ : ℝ) (v : Prefix k d) : ℝ := 2*v.1.val+χ⁻¹

end RiffleUpperV2.Anchor
