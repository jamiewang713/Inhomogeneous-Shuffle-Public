import Contracts.v1.FactorialOccupancy
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Factorial

lemma bonferroni_succ (m n : ℕ) (hm : 1 ≤ m) :
    bonferroni (m+1) n = bonferroni m n + (-1 : ℝ)^(m+1) * m * n.choose (m+1) := by
  unfold bonferroni
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m+1)]
  simp

lemma bonferroni_small (m n : ℕ) (hn : n < 2) : bonferroni m n = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
  simp [Nat.choose_eq_zero_of_lt (by omega : n < r)]

/-- A positive closed remainder avoids any estimate on large counts. -/
lemma bonferroni_closed (m n : ℕ) :
    bonferroni (m+1) (n+2) = 1 + (-1 : ℝ)^(m+1) *
      ((n.choose m : ℝ) + m * (n+1).choose (m+1)) := by
  induction m with
  | zero => simp [bonferroni]
  | succ m ih =>
    rw [show m+1+1 = (m+1)+1 by omega, bonferroni_succ (m+1) (n+2) (by omega), ih]
    have hPascal : ((n+2).choose (m+2) : ℝ) =
        (n.choose m : ℝ) + (n.choose (m+1) : ℝ) + ((n+1).choose (m+2) : ℝ) := by
      rw [Nat.choose_succ_succ (n+1) (m+1), Nat.choose_succ_succ n m]
      push_cast
      ring
    rw [hPascal]
    rw [Nat.choose_succ_succ n m]
    push_cast
    simp only [pow_succ]
    ring

lemma bonferroniRemainder_nonneg (m n : ℕ) : 0 ≤ bonferroniRemainder m n := by
  unfold bonferroniRemainder
  positivity

theorem bonferroniSandwich : Targets.BonferroniSandwich := by
  intro m hm heven n
  by_cases hn : n < 2
  · rw [bonferroni_small m n hn, if_neg (by omega)]
    exact ⟨by norm_num, by simpa using bonferroniRemainder_nonneg m n⟩
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hpow : (-1 : ℝ)^(2+b) = 1 := heven.neg_one_pow
  have hpow' : (-1 : ℝ)^(b+1) = -1 := by
    have : (-1 : ℝ)^(b+1) * (-1) = 1 := by
      calc
        (-1 : ℝ)^(b+1) * (-1) = (-1 : ℝ)^(b+1+1) := (pow_succ _ _).symm
        _ = 1 := by rw [show b+1+1 = 2+b by omega]; exact hpow
    linarith
  have hupper := bonferroni_closed (b+1) a
  have hlower := bonferroni_closed b a
  have hstep := bonferroni_succ (b+1) (a+2) (by omega)
  have hc0 : 0 ≤ (a.choose (b+1) : ℝ) + (b+1 : ℕ) * (a+1).choose (b+2) := by positivity
  have hc1 : 0 ≤ (a.choose b : ℝ) + b * (a+1).choose (b+1) := by positivity
  have hpow'' : (-1 : ℝ)^(b+1+1) = 1 := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hpow
  rw [hpow''] at hupper hstep
  rw [hpow'] at hlower
  simp only [one_mul] at hupper hstep
  simp only [show 2 ≤ 2+a by omega, if_true]
  change 0 ≤ bonferroni (2+b) (2+a) - 1 ∧
    bonferroni (2+b) (2+a) - 1 ≤ ((2+b-1 : ℕ) : ℝ) * ((2+a).choose (2+b) : ℝ)
  have h1 : bonferroni (2+b) (2+a) = bonferroni (b+1+1) (a+2) := by congr 1 <;> omega
  rw [h1]
  have h2 : ((2+b-1 : ℕ) : ℝ) * ((2+a).choose (2+b) : ℝ) =
      (b+1 : ℕ) * ((a+2).choose (b+1+1) : ℝ) := by
    rw [show 2+b-1 = b+1 by omega, show 2+a = a+2 by omega, show 2+b = b+1+1 by omega]
  rw [h2]
  constructor <;> nlinarith

lemma product_remainder (u v a b dx dy : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hu : 0 ≤ u-a ∧ u-a ≤ dx) (hv : 0 ≤ v-b ∧ v-b ≤ dy) :
    0 ≤ u*v-a*b ∧ u*v-a*b ≤ dx+dy+dx*dy := by
  have hdx : 0 ≤ dx := hu.1.trans hu.2
  have hdy : 0 ≤ dy := hv.1.trans hv.2
  have he := mul_nonneg hu.1 hv.1
  have he' := mul_le_mul hu.2 hv.2 hv.1 hdx
  have hax := mul_nonneg ha0 hv.1
  have hby := mul_nonneg hb0 hu.1
  have hax' : a*(v-b) ≤ dy := (mul_le_mul_of_nonneg_right ha1 hv.1).trans (by simpa using hv.2)
  have hby' : b*(u-a) ≤ dx := (mul_le_mul_of_nonneg_right hb1 hu.1).trans (by simpa using hu.2)
  constructor <;> nlinarith

theorem bonferroniProduct : Targets.BonferroniProduct := by
  intro m hm heven x y
  have hx := bonferroniSandwich m hm heven x
  have hy := bonferroniSandwich m hm heven y
  have hh := product_remainder (bonferroni m x) (bonferroni m y)
    (if 2 ≤ x then 1 else 0) (if 2 ≤ y then 1 else 0)
    (bonferroniRemainder m x) (bonferroniRemainder m y)
    (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
    (by split_ifs <;> norm_num) (by split_ifs <;> norm_num) hx hy
  simpa only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    ← ite_and, and_comm] using hh

end RiffleLowerV2.Factorial
