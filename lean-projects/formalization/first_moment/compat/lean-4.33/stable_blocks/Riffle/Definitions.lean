import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! Exact definitions frozen in spec/FROZEN_SPEC.md, revision 1. -/
namespace Riffle

abbrev Word := List ℕ

def digit (x : Word) (i : ℕ) : ℕ := x[i]?.getD 0

def parent (x : Word) : Word := x.take (x.length - 1)

def join (y z : Word) : Word := if z.length ≤ y.length then y else z

structure Model where
  N : ℕ
  K : ℕ
  k : ℕ
  n : ℕ → ℕ → ℕ
  one_lt_N : 1 < N
  two_le_k : 2 ≤ k
  sum_counts : ∀ i, i < K → ∑ a ∈ Finset.range k, n i a = N

def Legal (D : Model) (x : Word) : Prop :=
  x.length ≤ D.K ∧ ∀ i, i < x.length → digit x i < D.k ∧ 0 < D.n i (digit x i)

def Full (D : Model) (x : Word) : Prop := Legal D x ∧ x.length = D.K

def Desc (D : Model) (w : Word) : Set Word := {x | Legal D x ∧ w <+: x}

def Cylinder (D : Model) (x : Word) : Set Word := {ω | Full D ω ∧ x <+: ω}

def FamilyCylinder (D : Model) (U : Set Word) : Set Word :=
  {ω | ∃ x ∈ U, ω ∈ Cylinder D x}

structure Setup (D : Model) where
  w : Word
  w_legal : Legal D w
  b : ℝ
  chi : ℝ
  chi_pos : 0 < chi
  chi_lt : chi < 1 / (D.k : ℝ)
  C : ℝ
  C_pos : 0 < C
  delta : ℝ
  delta_pos : 0 < delta

noncomputable def prob (D : Model) (i a : ℕ) : NNReal :=
  (D.n i a : NNReal) / (D.N : NNReal)

abbrev FullIndex (D : Model) := Fin D.K → Fin D.k

def fullList {D : Model} (ω : FullIndex D) : Word := List.ofFn (fun i => (ω i).val)

noncomputable def weight (D : Model) (ω : FullIndex D) : NNReal :=
  ∏ i : Fin D.K, prob D i (ω i)

noncomputable def expectedCount (D : Model) (E : Set Word) : NNReal := by
  classical
  exact (D.N : NNReal) * ∑ ω : FullIndex D, if fullList ω ∈ E then weight D ω else 0

inductive Side where
  | left
  | right
  deriving DecidableEq

noncomputable def largeDigits {D : Model} (A : Setup D) (i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range D.k).filter (fun a => A.chi ≤ (prob D i a : ℝ))

noncomputable def leftIndex {D : Model} (A : Setup D) (i : ℕ) : ℕ := by
  classical
  exact if h : (largeDigits A i).Nonempty then (largeDigits A i).min' h else 0

noncomputable def rightIndex {D : Model} (A : Setup D) (i : ℕ) : ℕ := by
  classical
  exact if h : (largeDigits A i).Nonempty then (largeDigits A i).max' h else 0

noncomputable def crossDigit {D : Model} (A : Setup D) (s : Side) (i a : ℕ) : Prop :=
  match s with
  | .left => leftIndex A i < a
  | .right => a < rightIndex A i

noncomputable def Cross {D : Model} (A : Setup D) (s : Side) (x : Word) (i : ℕ) : Prop :=
  crossDigit A s i (digit x i)

def BoundaryCut (D : Model) (w : Word) (q : ℕ → ℕ → Prop) : Set Word :=
  {x | x ∈ Desc D w ∧
    ((w.length < x.length ∧ q (x.length - 1) (digit x (x.length - 1)) ∧
      ∀ i, w.length ≤ i → i < x.length - 1 → ¬q i (digit x i)) ∨
     (x.length = D.K ∧ ∀ i, w.length ≤ i → i < D.K → ¬q i (digit x i)))}

noncomputable def Boundary {D : Model} (A : Setup D) (s : Side) : Set Word :=
  BoundaryCut D A.w (crossDigit A s)

noncomputable def selectCut (D : Model) (w : Word) (q : ℕ → ℕ → Prop) (ω : Word) : Word := by
  classical
  exact if h : ∃ i, w.length ≤ i ∧ i < D.K ∧ q i (digit ω i) then
    ω.take (Nat.find h + 1) else ω.take D.K

noncomputable def selected {D : Model} (A : Setup D) (s : Side) (ω : Word) : Word :=
  selectCut D A.w (crossDigit A s) ω

noncomputable def violations {D : Model} (A : Setup D) (s : Side) (x : Word) : ℕ := by
  classical
  exact ((Finset.Ico A.w.length x.length).filter (fun i => match s with
    | .left => digit x i < leftIndex A i
    | .right => rightIndex A i < digit x i)).card

noncomputable def Admissible {D : Model} (A : Setup D) (s : Side) : Set Word :=
  {x | x ∈ Boundary A s ∧
    (violations A s x : ℝ) ≤ A.C / Real.log (1 / A.chi) * Real.log (D.N : ℝ)}

def pairDesc {D : Model} (A : Setup D) (y z : Word) : Set Word :=
  {x | x ∈ Desc D A.w ∧ y <+: x ∧ z <+: x}

def Compatible {D : Model} (A : Setup D) (y z : Word) : Prop :=
  (pairDesc A y z).Nonempty

noncomputable def RawPair {D : Model} (A : Setup D) (y z : Word) : Prop :=
  y ∈ Boundary A .left ∧ z ∈ Boundary A .right ∧ Compatible A y z

noncomputable def AdmissiblePair {D : Model} (A : Setup D) (y z : Word) : Prop :=
  y ∈ Admissible A .left ∧ z ∈ Admissible A .right ∧ Compatible A y z

def Terminal (D : Model) (y z : Word) : Prop := y.length = D.K ∨ z.length = D.K

def Piece {D : Model} (A : Setup D) (s : Side) (x : Word) (i : ℕ) : Set Word :=
  {σ | σ ∈ Desc D A.w ∧ σ.length = x.length ∧ σ.take i = x.take i ∧
    match s with | .left => digit σ i < digit x i | .right => digit x i < digit σ i}

def PieceEvent {D : Model} (A : Setup D) (s : Side) (x : Word) (i : ℕ) : Set Word :=
  FamilyCylinder D (Piece A s x i)

noncomputable def sideMaximum {D : Model} (A : Setup D) (s : Side) (v x : Word) : NNReal :=
  (Finset.Ico A.w.length v.length).sup (fun i => expectedCount D (PieceEvent A s x i))

noncomputable def sideFluctuation {D : Model} (A : Setup D) (s : Side) (v x : Word) : ℝ :=
  Real.sqrt (sideMaximum A s v x : ℝ)

noncomputable def extendedLog (D : Model) (q : ℝ) : WithBot ℝ :=
  if q = 0 then ⊥ else ↑(Real.log q / Real.log (D.N : ℝ))

noncomputable def cFAt {D : Model} (A : Setup D) (v x : Word) : WithBot ℝ :=
  min (extendedLog D (sideFluctuation A .left v x))
      (extendedLog D (sideFluctuation A .right v x))

noncomputable def cF {D : Model} (A : Setup D) (y z : Word) : WithBot ℝ :=
  cFAt A (join y z) (join y z)

noncomputable def Retained {D : Model} (A : Setup D) (y z : Word) : Prop :=
  Compatible A y z ∧ (Terminal D y z ∨ cF A y z ≠ ⊥)

noncomputable def cL {D : Model} (A : Setup D) (x : Word) : ℝ :=
  A.b - (∑ i ∈ Finset.Ico A.w.length x.length,
    Real.log ((D.N : ℝ) / (D.n i (digit x i) : ℝ))) / Real.log (D.N : ℝ)

noncomputable def Stop {D : Model} (A : Setup D) (y z x : Word) : Prop :=
  (cL A x : WithBot ℝ) < cF A y z + (A.delta : WithBot ℝ)

noncomputable def Gamma {D : Model} (A : Setup D) (y z : Word) : Set Word :=
  {x | x ∈ pairDesc A y z ∧ Stop A y z x ∧ ¬ Stop A y z (parent x)}

noncomputable def Lambda {D : Model} (A : Setup D) (y z : Word) : Set Word :=
  {x | x ∈ pairDesc A y z ∧ x.length = D.K ∧ ¬ Stop A y z x}

noncomputable def Stable {D : Model} (A : Setup D) (y z : Word) : Set Word := by
  classical
  exact if Terminal D y z then {join y z}
  else if Stop A y z (join y z) then {join y z} else Gamma A y z ∪ Lambda A y z

def PrefixAntichain (U : Set Word) : Prop := ∀ x ∈ U, ∀ y ∈ U, x <+: y → x = y

def LexLE (x y : Word) : Prop := x = y ∨ List.Lex (· < ·) x y

def RankSet {M : ℕ} (rows : Fin M → Word) (E : Set Word) : Set (Fin M) := rows ⁻¹' E

def SortedRows {M : ℕ} (rows : Fin M → Word) : Prop :=
  ∀ i j, i ≤ j → LexLE (rows i) (rows j)

noncomputable def GenericCut (D : Model) (v : Word) (Q : Word → Prop) : Set Word := by
  classical
  exact if Q v ∨ v.length = D.K then {v} else
    {x | x ∈ Desc D v ∧ ((Q x ∧ ¬Q (parent x)) ∨ (x.length = D.K ∧ ¬Q x))}

end Riffle
