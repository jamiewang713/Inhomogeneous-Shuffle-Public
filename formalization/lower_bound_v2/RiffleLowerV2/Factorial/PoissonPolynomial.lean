import RiffleLowerV2.Factorial.Bonferroni
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.Distributions.Poisson.Basic

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Factorial
set_option maxHeartbeats 1000000

def poissonPolynomial (m : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 m, (-1 : ℝ)^r * (r-1 : ℕ) * t^r / (r.factorial : ℝ)

def poissonWeight (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t) * t^n / (n.factorial : ℝ)

lemma poissonWeight_nonneg (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poissonWeight t n := by
  unfold poissonWeight
  positivity

lemma hasSum_poissonWeight (t : ℝ) : HasSum (poissonWeight t) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp t).mul_left (Real.exp (-t)) using 1
  · ext n
    simp [poissonWeight, mul_div_assoc]
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    simp

/-- Exact scalar binomial moment, proved by shifting the exponential series. -/
lemma hasSum_poissonWeight_choose (t : ℝ) (r : ℕ) :
    HasSum (fun n => poissonWeight t n * (n.choose r : ℝ)) (t^r / (r.factorial : ℝ)) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp t).mul_left
    (Real.exp (-t) * t^r / (r.factorial : ℝ))
  have hshift (n : ℕ) : poissonWeight t (n+r) * ((n+r).choose r : ℝ) =
      (Real.exp (-t) * t^r / (r.factorial : ℝ)) * (t^n / (n.factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : r ≤ n+r)]
    simp only [Nat.add_sub_cancel_right]
    unfold poissonWeight
    rw [pow_add]
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hr : (r.factorial : ℝ) ≠ 0 := by positivity
    have hnr : ((n+r).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have hs' : HasSum (fun n => poissonWeight t (n+r) * ((n+r).choose r : ℝ))
      (t^r / (r.factorial : ℝ)) := by
    convert! hs using 1
    · ext n
      exact hshift n
    · rw [← Real.exp_eq_exp_ℝ]
      have hexp : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
      calc
        t^r / (r.factorial : ℝ) = (Real.exp (-t) * Real.exp t) * (t^r / (r.factorial : ℝ)) := by rw [hexp]; ring
        _ = _ := by ring
  have hp : ∑ n ∈ Finset.range r, poissonWeight t n * (n.choose r : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hn)]
  have hall := HasSum.sum_range_add (f := fun n => poissonWeight t n * (n.choose r : ℝ))
    (k := r) hs'
  rw [hp, zero_add] at hall
  exact hall

lemma hasSum_poissonWeight_indicator (t : ℝ) :
    HasSum (fun n => poissonWeight t n * (if 2 ≤ n then 1 else 0)) (poissonCollision t) := by
  have ht := (hasSum_nat_add_iff' (f := poissonWeight t) 2).mpr (hasSum_poissonWeight t)
  have htail : HasSum (fun n => poissonWeight t (n+2)) (poissonCollision t) := by
    convert! ht using 1
    simp [poissonCollision, poissonWeight, Finset.sum_range_succ]
    ring
  have hs : HasSum (fun n => poissonWeight t (n+2) * (if 2 ≤ n+2 then (1 : ℝ) else 0))
      (poissonCollision t) := by simpa using htail
  have hall := HasSum.sum_range_add
    (f := fun n => poissonWeight t n * (if 2 ≤ n then (1 : ℝ) else 0)) (k := 2) hs
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, show ¬2 ≤ 0 by omega,
    show ¬2 ≤ 1 by omega, if_false, mul_zero, add_zero, zero_add] using hall

lemma poissonCollision_bounds (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ poissonCollision t ∧ poissonCollision t ≤ 1 := by
  have hs := hasSum_poissonWeight_indicator t
  constructor
  · exact hs.nonneg (fun n => mul_nonneg (poissonWeight_nonneg t ht n) (by split_ifs <;> norm_num))
  · exact hasSum_le (fun n => by split_ifs <;> simp [poissonWeight_nonneg t ht n]) hs (hasSum_poissonWeight t)

lemma hasSum_poissonWeight_bonferroni (m : ℕ) (t : ℝ) :
    HasSum (fun n => poissonWeight t n * bonferroni m n) (poissonPolynomial m t) := by
  have hs := hasSum_sum (s := Finset.Icc 2 m) (fun r _ =>
    (hasSum_poissonWeight_choose t r).mul_left ((-1 : ℝ)^r * (r-1 : ℕ)))
  convert! hs using 1
  · ext n
    unfold bonferroni
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  · unfold poissonPolynomial
    apply Finset.sum_congr rfl
    intro r hr
    ring

lemma hasSum_poissonWeight_remainder (m : ℕ) (t : ℝ) :
    HasSum (fun n => poissonWeight t n * bonferroniRemainder m n) (poissonRemainder m t) := by
  convert! (hasSum_poissonWeight_choose t m).mul_left ((m-1 : ℕ) : ℝ) using 1
  · ext n
    unfold bonferroniRemainder
    ring
  · unfold poissonRemainder
    ring

/-- The pointwise finite sandwich is summed over all natural counts. -/
lemma poissonPolynomial_sandwich (m : ℕ) (hm : 2 ≤ m) (heven : Even m)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ poissonPolynomial m t - poissonCollision t ∧
      poissonPolynomial m t - poissonCollision t ≤ poissonRemainder m t := by
  have hs := (hasSum_poissonWeight_bonferroni m t).sub (hasSum_poissonWeight_indicator t)
  constructor
  · apply hs.nonneg
    intro n
    have hh := mul_nonneg (poissonWeight_nonneg t ht n) (bonferroniSandwich m hm heven n).1
    nlinarith
  · apply hasSum_le _ hs (hasSum_poissonWeight_remainder m t)
    intro n
    have hh := mul_le_mul_of_nonneg_left (bonferroniSandwich m hm heven n).2
      (poissonWeight_nonneg t ht n)
    nlinarith

lemma poissonCoefficientSum_le (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ r ∈ Finset.Icc 2 m, (r-1 : ℕ) * t^r / (r.factorial : ℝ)) ≤
      (1+t) * Real.exp t := by
  have hterm (r : ℕ) : ((r-1 : ℕ) : ℝ) * t^r / (r.factorial : ℝ) ≤
      (r : ℝ) * t^r / (r.factorial : ℝ) := by
    gcongr
    exact_mod_cast Nat.sub_le r 1
  have hsub : Finset.Icc 2 m ⊆ Finset.range (m+1) := by
    intro r hr
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  have hsum : (∑ r ∈ Finset.range (m+1), (r : ℝ)*t^r/(r.factorial : ℝ)) =
      t * ∑ r ∈ Finset.range m, t^r/(r.factorial : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hfac : (r.factorial : ℝ) ≠ 0 := by positivity
    have hr1 : (r : ℝ)+1 ≠ 0 := by positivity
    field_simp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 m, (r : ℝ)*t^r/(r.factorial : ℝ) := Finset.sum_le_sum (fun r _ => hterm r)
    _ ≤ ∑ r ∈ Finset.range (m+1), (r : ℝ)*t^r/(r.factorial : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => by positivity)
    _ = t * ∑ r ∈ Finset.range m, t^r/(r.factorial : ℝ) := hsum
    _ ≤ t * Real.exp t := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg ht m) ht
    _ ≤ (1+t) * Real.exp t := by nlinarith [Real.exp_pos t]

end RiffleLowerV2.Factorial
