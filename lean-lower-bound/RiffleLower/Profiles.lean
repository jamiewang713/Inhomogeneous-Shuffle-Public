import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

namespace RiffleLower

open Finset

noncomputable def digitCount {Time Cell Digit : Type*}
    [Fintype Time] [Fintype Cell] [Fintype Digit]
    (cell : Time → Cell) (word : Time → Digit) (c : Cell) (d : Digit) : ℕ := by
  classical
  exact (univ.filter fun t => cell t = c ∧ word t = d).card

noncomputable def cellCount {Time Cell : Type*} [Fintype Time] [Fintype Cell]
    (cell : Time → Cell) (c : Cell) : ℕ := by
  classical
  exact (univ.filter fun t => cell t = c).card

noncomputable def digitWordMass {Time Digit : Type*} [Fintype Time] [Fintype Digit]
    (p : Time → Digit → ℝ) (word : Time → Digit) : ℝ := ∏ t, p t (word t)

noncomputable def digitWordCost {Time Digit : Type*} [Fintype Time] [Fintype Digit]
    (p : Time → Digit → ℝ) (word : Time → Digit) : ℝ := -∑ t, Real.log (p t (word t))

noncomputable def profileMass {Time Cell Digit : Type*}
    [Fintype Time] [Fintype Cell] [Fintype Digit]
    (r : Cell → Digit → ℝ) (cell : Time → Cell) (word : Time → Digit) : ℝ :=
  ∏ c, ∏ d, (r c d) ^ digitCount cell word c d

/-- D1a: digits partition the times in a fixed cell. -/
theorem digitCount_cell_sum {Time Cell Digit : Type*}
    [Fintype Time] [Fintype Cell] [Fintype Digit]
    (cell : Time → Cell) (word : Time → Digit) (c : Cell) :
    ∑ d, digitCount cell word c d = cellCount cell c := by
  classical
  simp only [digitCount, cellCount, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : cell t = c <;> simp [h]

/-- D1b: the cell and digit profile accounts for every time exactly once. -/
theorem digitCount_total {Time Cell Digit : Type*}
    [Fintype Time] [Fintype Cell] [Fintype Digit]
    (cell : Time → Cell) (word : Time → Digit) :
    ∑ c, ∑ d, digitCount cell word c d = Fintype.card Time := by
  classical
  simp_rw [digitCount_cell_sum]
  simp only [cellCount, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

/-- D2: exact product regrouping by time-cell digit counts. -/
theorem profile_product_exact {Time Cell Digit : Type*}
    [Fintype Time] [Fintype Cell] [Fintype Digit]
    (r : Cell → Digit → ℝ) (cell : Time → Cell) (word : Time → Digit) :
    digitWordMass (fun t d => r (cell t) d) word = profileMass r cell word := by
  classical
  unfold digitWordMass profileMass digitCount
  symm
  calc
    (∏ c, ∏ d, r c d ^ (univ.filter fun t => cell t = c ∧ word t = d).card) =
        ∏ c, ∏ d, ∏ t ∈ univ.filter (fun t => cell t = c ∧ word t = d), r c d := by
      simp only [Finset.prod_const]
    _ = ∏ c, ∏ t ∈ univ.filter (fun t => cell t = c), r c (word t) := by
      apply Finset.prod_congr rfl
      intro c _
      simpa only [Finset.filter_filter] using
        Finset.prod_fiberwise' (univ.filter fun t => cell t = c) word (r c)
    _ = ∏ c, ∏ t ∈ univ.filter (fun t => cell t = c), r (cell t) (word t) := by
      apply Finset.prod_congr rfl
      intro c _
      apply Finset.prod_congr rfl
      intro t ht
      rw [(mem_filter.mp ht).2]
    _ = ∏ t, r (cell t) (word t) :=
      Finset.prod_fiberwise univ cell (fun t => r (cell t) (word t))

/-- D3: positive selected digits give the exact logarithmic word cost. -/
theorem legal_word_log_mass {Time Digit : Type*} [Fintype Time] [Fintype Digit]
    (p : Time → Digit → ℝ) (word : Time → Digit)
    (hpos : ∀ t, 0 < p t (word t)) :
    Real.log (digitWordMass p word) = -digitWordCost p word := by
  simp only [digitWordMass, digitWordCost, neg_neg]
  exact Real.log_prod univ (fun t => p t (word t)) (fun t _ => ne_of_gt (hpos t))

/-- D4: a choice of maximal digits maximizes the finite full-word product. -/
theorem maximal_digit_word_mass {Time Digit : Type*} [Fintype Time] [Fintype Digit]
    (p : Time → Digit → ℝ) (star word : Time → Digit)
    (hnonneg : ∀ t d, 0 ≤ p t d) (hmax : ∀ t d, p t d ≤ p t (star t)) :
    digitWordMass p word ≤ digitWordMass p star := by
  exact Finset.prod_le_prod (fun t _ => hnonneg t (word t)) (fun t _ => hmax t (word t))

end RiffleLower
