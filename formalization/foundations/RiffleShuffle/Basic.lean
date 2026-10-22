import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Frozen finite data and definitions. See ../CONTRACT.md and ../FREEZE.md. -/

noncomputable section
open scoped BigOperators
namespace RiffleShuffle

structure PileProfile (N k K : ℕ) where
  count : Fin K → Fin k → ℕ
  deck_pos : 0 < N
  alphabet_two : 2 ≤ k
  total : ∀ j, ∑ a, count j a = N

def NormalizedProfile (k : ℕ) :=
  {p : Fin k → ℝ // (∀ a, 0 ≤ p a ∧ p a ≤ 1) ∧ ∑ a, p a = 1}

def PileProfile.countAt {N k K : ℕ} (P : PileProfile N k K)
    (j : ℕ) (a : Fin k) : ℕ :=
  if h : j < K then P.count ⟨j, h⟩ a else 0

def PileProfile.probAt {N k K : ℕ} (P : PileProfile N k K)
    (j : ℕ) (a : Fin k) : ℝ := (P.countAt j a : ℝ) / (N : ℝ)

abbrev Word (k m : ℕ) := List.Vector (Fin k) m

instance wordLinearOrder {k m : ℕ} : LinearOrder (Word k m) :=
  inferInstanceAs (LinearOrder {l : List (Fin k) // l.length = m})

def Prefix {k m n : ℕ} (x : Word k m) (y : Word k n) : Prop :=
  x.toList <+: y.toList

def emptyWord (k : ℕ) : Word k 0 := List.Vector.nil

def truncate {k m n : ℕ} (h : m ≤ n) (y : Word k n) : Word k m :=
  ⟨y.toList.take m, by simp only [List.length_take, List.Vector.toList_length, Nat.min_eq_left h]⟩

def appendDigit {k m : ℕ} (x : Word k m) (a : Fin k) : Word k (m + 1) :=
  ⟨x.toList ++ [a], by simp⟩

def Legal {N k K m : ℕ} (P : PileProfile N k K) (x : Word k m) : Prop :=
  m ≤ K ∧ ∀ j : Fin m, 0 < P.countAt j.val (x.get j)

def mass {N k K m : ℕ} (P : PileProfile N k K) (x : Word k m) : ℝ :=
  ∏ j : Fin m, P.probAt j.val (x.get j)

abbrev RawPrefix (k K : ℕ) := Σ m : Fin (K + 1), Word k m.val

def Node {N k K : ℕ} (P : PileProfile N k K) :=
  {x : RawPrefix k K // Legal P x.2}

abbrev FullWord {N k K : ℕ} (P : PileProfile N k K) :=
  {x : Word k K // Legal P x}

def Node.depth {N k K : ℕ} {P : PileProfile N k K} (x : Node P) : ℕ := x.1.1.val

def Node.word {N k K : ℕ} {P : PileProfile N k K} (x : Node P) : Word k x.depth := x.1.2

def Node.toList {N k K : ℕ} {P : PileProfile N k K} (x : Node P) : List (Fin k) :=
  x.word.toList

def Node.IsPrefix {N k K : ℕ} {P : PileProfile N k K} (x y : Node P) : Prop :=
  x.toList <+: y.toList

def Child {N k K : ℕ} {P : PileProfile N k K} (x y : Node P) : Prop :=
  x.IsPrefix y ∧ y.depth = x.depth + 1

def cylinder {N k K : ℕ} {P : PileProfile N k K} (x : Node P) : Set (FullWord P) :=
  {s | x.toList <+: s.1.toList}

def PrefixAntichain {N k K : ℕ} {P : PileProfile N k K} (U : Set (Node P)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, x.IsPrefix y → x = y

def Covers {N k K : ℕ} {P : PileProfile N k K} (U : Set (Node P)) : Prop :=
  ∀ s : FullWord P, ∃ x ∈ U, s ∈ cylinder x

end RiffleShuffle
