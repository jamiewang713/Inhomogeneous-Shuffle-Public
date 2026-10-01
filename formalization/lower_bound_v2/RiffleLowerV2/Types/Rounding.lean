import RiffleLowerV2.Shared.Geometry
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Types

private def extendedWeight {k : ℕ} (q : Fin k → ℝ) (a : ℕ) : ℝ :=
  if h : a < k then q ⟨a, h⟩ else 0

/-- Prefix masses in the fixed digit order. -/
def roundingPrefix {k : ℕ} (n : ℕ) (q : Fin k → ℝ) (a : ℕ) : ℝ :=
  ∑ b ∈ Finset.range a, (n : ℝ) * extendedWeight q b

/-- Deterministic rounding by differences of consecutive cumulative floors. -/
def roundedCount {k : ℕ} (n : ℕ) (q : Fin k → ℝ) (l : Fin k) : ℕ :=
  ⌊roundingPrefix n q (l.val + 1)⌋₊ - ⌊roundingPrefix n q l.val⌋₊

private theorem extendedWeight_nonneg {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ l, 0 ≤ q l) (a : ℕ) : 0 ≤ extendedWeight q a := by
  unfold extendedWeight
  split_ifs with h
  · exact hq ⟨a, h⟩
  · rfl

theorem roundingPrefix_nonneg {k : ℕ} (n : ℕ) (q : Fin k → ℝ)
    (hq : ∀ l, 0 ≤ q l) (a : ℕ) : 0 ≤ roundingPrefix n q a :=
  Finset.sum_nonneg fun b _ => mul_nonneg (Nat.cast_nonneg n) (extendedWeight_nonneg q hq b)

theorem roundingPrefix_succ {k : ℕ} (n : ℕ) (q : Fin k → ℝ) (l : Fin k) :
    roundingPrefix n q (l.val + 1) = roundingPrefix n q l.val + (n : ℝ) * q l := by
  simp [roundingPrefix, Finset.sum_range_succ, extendedWeight, l.isLt]

private theorem roundingPrefix_step {k : ℕ} (n : ℕ) (q : Fin k → ℝ)
    (hq : ∀ l, 0 ≤ q l) (a : ℕ) :
    roundingPrefix n q a ≤ roundingPrefix n q (a + 1) := by
  unfold roundingPrefix
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (extendedWeight_nonneg q hq a))

theorem roundingPrefix_total {k : ℕ} (n : ℕ) (q : Fin k → ℝ)
    (hsum : ∑ l, q l = 1) : roundingPrefix n q k = n := by
  unfold roundingPrefix
  rw [Finset.sum_range]
  simp only [extendedWeight, Fin.isLt, dite_true]
  rw [← Finset.mul_sum, hsum, mul_one]

theorem roundedCount_sum {k : ℕ} (n : ℕ) (q : Fin k → ℝ)
    (hq : ∀ l, 0 ≤ q l) (hsum : ∑ l, q l = 1) :
    ∑ l, roundedCount n q l = n := by
  have telescopes (a : ℕ) :
      (∑ b ∈ Finset.range a,
        (⌊roundingPrefix n q (b + 1)⌋₊ - ⌊roundingPrefix n q b⌋₊)) =
      ⌊roundingPrefix n q a⌋₊ := by
    induction a with
    | zero => simp [roundingPrefix]
    | succ a ih =>
        rw [Finset.sum_range_succ, ih]
        have h := Nat.floor_mono (roundingPrefix_step n q hq a)
        omega
  unfold roundedCount
  calc
    _ = ∑ b ∈ Finset.range k,
        (⌊roundingPrefix n q (b + 1)⌋₊ - ⌊roundingPrefix n q b⌋₊) :=
      (Finset.sum_range (n := k) (fun b : ℕ =>
        ⌊roundingPrefix n q (b + 1)⌋₊ - ⌊roundingPrefix n q b⌋₊)).symm
    _ = ⌊roundingPrefix n q k⌋₊ := telescopes k
    _ = n := by rw [roundingPrefix_total n q hsum, Nat.floor_natCast]

theorem roundedCount_zero {k : ℕ} (n : ℕ) (q : Fin k → ℝ)
    (l : Fin k) (hl : q l = 0) : roundedCount n q l = 0 := by
  simp [roundedCount, roundingPrefix_succ, hl]

theorem roundedCount_error_lt {k : ℕ} (n : ℕ) (q : Fin k → ℝ)
    (hq : ∀ l, 0 ≤ q l) (l : Fin k) :
    |(roundedCount n q l : ℝ) - (n : ℝ) * q l| < 1 := by
  have hle := Nat.floor_mono (roundingPrefix_step n q hq l.val)
  have ha := Nat.floor_le (roundingPrefix_nonneg n q hq l.val)
  have hb := Nat.floor_le (roundingPrefix_nonneg n q hq (l.val + 1))
  have ha' := Nat.lt_floor_add_one (roundingPrefix n q l.val)
  have hb' := Nat.lt_floor_add_one (roundingPrefix n q (l.val + 1))
  have hstep := roundingPrefix_succ n q l
  unfold roundedCount
  rw [Nat.cast_sub hle, abs_lt]
  constructor <;> linarith

theorem roundedCount_error {k : ℕ} (n : ℕ) (q : Fin k → ℝ)
    (hq : ∀ l, 0 ≤ q l) (l : Fin k) :
    |(roundedCount n q l : ℝ) - (n : ℝ) * q l| ≤ 1 :=
  (roundedCount_error_lt n q hq l).le

theorem exists_supported_rounding {k : ℕ} (n : ℕ) (q : Fin k → ℝ)
    (hq : ∀ l, 0 ≤ q l) (hsum : ∑ l, q l = 1) :
    ∃ c : Fin k → ℕ,
      (∑ l, c l = n) ∧
      (∀ l, q l = 0 → c l = 0) ∧
      (∀ l, |(c l : ℝ) - (n : ℝ) * q l| ≤ 1) :=
  ⟨roundedCount n q, roundedCount_sum n q hq hsum,
    roundedCount_zero n q, roundedCount_error n q hq⟩

end RiffleLowerV2.Types
