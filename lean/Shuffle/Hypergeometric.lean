import Shuffle.FiniteLaw
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.NatAntidiagonal

noncomputable section
open scoped BigOperators

namespace Shuffle

structure HypergeomParams where
  population : ℕ
  marked : ℕ
  draws : ℕ
  marked_le : marked ≤ population
  draws_le : draws ≤ population

namespace HypergeomParams

def weight (p : HypergeomParams) (q : Fin (p.draws + 1)) : ℝ :=
  (p.marked.choose q.val : ℝ) *
    ((p.population - p.marked).choose (p.draws - q.val) : ℝ) /
    (p.population.choose p.draws : ℝ)

def mean (p : HypergeomParams) : ℝ :=
  (p.marked : ℝ) * (p.draws : ℝ) / (p.population : ℝ)

def varianceFormula (p : HypergeomParams) : ℝ :=
  (p.marked : ℝ) * (p.draws : ℝ) * ((p.population : ℝ) - (p.marked : ℝ)) *
    ((p.population : ℝ) - (p.draws : ℝ)) /
    ((p.population : ℝ) ^ 2 * ((p.population : ℝ) - 1))

theorem denominator_pos (p : HypergeomParams) :
    0 < (p.population.choose p.draws : ℝ) := by
  exact_mod_cast Nat.choose_pos p.draws_le

theorem weight_nonneg (p : HypergeomParams) (q : Fin (p.draws + 1)) :
    0 ≤ p.weight q := by
  unfold weight
  positivity

theorem weight_sum (p : HypergeomParams) : ∑ q, p.weight q = 1 := by
  have h : ∑ q : Fin (p.draws + 1),
      p.marked.choose q.val * (p.population - p.marked).choose (p.draws - q.val) =
      p.population.choose p.draws := by
    rw [Fin.sum_univ_eq_sum_range (fun q : ℕ =>
      p.marked.choose q * (p.population - p.marked).choose (p.draws - q))]
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => p.marked.choose i * (p.population - p.marked).choose j) p.draws]
    rw [← Nat.add_choose_eq, Nat.add_sub_of_le p.marked_le]
  have hr : (∑ q : Fin (p.draws + 1),
      (p.marked.choose q.val : ℝ) *
        ((p.population - p.marked).choose (p.draws - q.val) : ℝ)) =
      (p.population.choose p.draws : ℝ) := by
    exact_mod_cast h
  simp only [weight, ← Finset.sum_div, hr, div_self (ne_of_gt p.denominator_pos)]

def law (p : HypergeomParams) : FiniteLaw (Fin (p.draws + 1)) where
  mass := p.weight
  mass_nonneg := p.weight_nonneg
  mass_sum := p.weight_sum

@[simp] theorem law_mass (p : HypergeomParams) (q : Fin (p.draws + 1)) :
    p.law.mass q = p.weight q := rfl

theorem weight_pos_iff (p : HypergeomParams) (q : Fin (p.draws + 1)) :
    0 < p.weight q ↔ q.val ≤ p.marked ∧ p.draws - q.val ≤ p.population - p.marked := by
  unfold weight
  rw [div_pos_iff_of_pos_right p.denominator_pos]
  norm_cast
  simp [mul_pos_iff, Nat.pos_iff_ne_zero, Nat.choose_eq_zero_iff]

def pointMass (p : HypergeomParams) (q : ℕ) : ℝ :=
  p.law.prob fun x => x.val = q

theorem pointMass_eq_weight (p : HypergeomParams) (q : Fin (p.draws + 1)) :
    p.pointMass q.val = p.weight q := by
  classical
  unfold pointMass FiniteLaw.prob
  rw [Finset.sum_eq_single q]
  · simp
  · intro x _ hx
    have hv : x.val ≠ q.val := fun h => hx (Fin.ext h)
    simp [hv]
  · simp

theorem pointMass_le_one (p : HypergeomParams) (q : ℕ) : p.pointMass q ≤ 1 :=
  p.law.prob_le_one _

theorem pointMass_eq_zero_of_lt (p : HypergeomParams) {q : ℕ} (hq : p.draws < q) :
    p.pointMass q = 0 := by
  unfold pointMass FiniteLaw.prob
  apply Finset.sum_eq_zero
  intro x _
  have hx : x.val ≠ q := by omega
  simp [hx]

theorem mean_nonneg (p : HypergeomParams) : 0 ≤ p.mean := by
  unfold mean
  positivity

end HypergeomParams
end Shuffle
