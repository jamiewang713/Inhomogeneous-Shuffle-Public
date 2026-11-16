import Shuffle.HypergeometricMoments
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic

/-!
Finite hypergeometric exponential transforms and concentration.
The exported targets in this file are governed by audit/FROZEN_CONTRACT.md.
-/

namespace Shuffle

noncomputable section
open scoped BigOperators

private theorem descFactorial_ratio_le_pow {N m : ℕ} (hm : m ≤ N) (r : ℕ) :
    (m.descFactorial r : ℝ) / (N.descFactorial r : ℝ) ≤ ((m : ℝ) / N) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      by_cases hrm : r < m
      · have hrN : r < N := lt_of_lt_of_le hrm hm
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le r) hrN)
        have hfactor : ((m - r : ℕ) : ℝ) / ((N - r : ℕ) : ℝ) ≤ (m : ℝ) / N := by
          rw [Nat.cast_sub (Nat.le_of_lt hrm), Nat.cast_sub (Nat.le_of_lt hrN)]
          have hrNr : (r : ℝ) < N := by exact_mod_cast hrN
          have hmr : (m : ℝ) ≤ N := by exact_mod_cast hm
          apply (div_le_div_iff₀ (sub_pos.mpr hrNr) hNpos).2
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) r) (sub_nonneg.mpr hmr)]
        rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul,
          mul_div_mul_comm, pow_succ']
        exact mul_le_mul hfactor ih (by positivity) (by positivity)
      · have hz : m.descFactorial (r + 1) = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        rw [hz, Nat.cast_zero, zero_div]
        positivity

private theorem binomial_sum_extended {q N : ℕ} (hq : q ≤ N) (u : ℝ) :
    (1 + u) ^ q = ∑ r ∈ Finset.range (N + 1), (q.choose r : ℝ) * u ^ r := by
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one]
  calc
    _ = ∑ r ∈ Finset.range (q + 1), (q.choose r : ℝ) * u ^ r := by
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hq)) (by
      intro r _ hr
      have hqr : q < r := by
        simp only [Finset.mem_range] at hr
        omega
      simp [Nat.choose_eq_zero_of_lt hqr])

namespace HypergeomParams

private def swapped (p : HypergeomParams) : HypergeomParams where
  population := p.population
  marked := p.draws
  draws := p.marked
  marked_le := p.draws_le
  draws_le := p.marked_le

private def extendedWeight (p : HypergeomParams) (q : ℕ) : ℝ :=
  if q ≤ p.draws then
    (p.marked.choose q : ℝ) * ((p.population - p.marked).choose (p.draws - q) : ℝ) /
      (p.population.choose p.draws : ℝ)
  else 0

private theorem expect_eq_extended_sum (p : HypergeomParams) (f : ℕ → ℝ) :
    p.law.expect (fun q => f q.val) =
      ∑ q ∈ Finset.range (p.population + 1), extendedWeight p q * f q := by
  unfold FiniteLaw.expect
  simp only [law_mass, weight]
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => (p.marked.choose q : ℝ) *
      ((p.population - p.marked).choose (p.draws - q) : ℝ) /
      (p.population.choose p.draws : ℝ) * f q) (p.draws + 1)]
  calc
    _ = ∑ q ∈ Finset.range (p.draws + 1), extendedWeight p q * f q := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqd : q ≤ p.draws := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
      simp only [extendedWeight, hqd, ↓reduceIte]
    _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ p.draws_le)) (by
      intro q _ hq
      have hqd : ¬q ≤ p.draws := by
        simp only [Finset.mem_range] at hq
        omega
      simp [extendedWeight, hqd])

private theorem extendedWeight_swapped (p : HypergeomParams) (q : ℕ) :
    extendedWeight p q = extendedWeight (swapped p) q := by
  by_cases hqm : q ≤ p.draws
  · by_cases hqK : q ≤ p.marked
    · simp only [extendedWeight, swapped, hqm, hqK, ↓reduceIte]
      by_cases hrest : p.draws - q ≤ p.population - p.marked
      · have hrest' : p.marked - q ≤ p.population - p.draws := by
          have := p.marked_le
          have := p.draws_le
          omega
        rw [Nat.cast_choose ℝ hqK, Nat.cast_choose ℝ hrest,
          Nat.cast_choose ℝ p.draws_le, Nat.cast_choose ℝ hqm,
          Nat.cast_choose ℝ hrest', Nat.cast_choose ℝ p.marked_le]
        have hres : p.population - p.marked - (p.draws - q) =
            p.population - p.draws - (p.marked - q) := by omega
        rw [hres]
        have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by
          exact_mod_cast Nat.factorial_ne_zero n
        field_simp
        simp_all only [ne_eq, hf, not_false_eq_true]
        ring
      · have hrest' : p.population - p.draws < p.marked - q := by
          have := p.marked_le
          have := p.draws_le
          omega
        simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hrest),
          Nat.choose_eq_zero_of_lt hrest']
    · simp [extendedWeight, swapped, hqm, hqK,
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hqK)]
  · by_cases hqK : q ≤ p.marked
    · simp [extendedWeight, swapped, hqm, hqK,
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hqm)]
    · simp [extendedWeight, swapped, hqm, hqK]

private theorem expect_swapped (p : HypergeomParams) (f : ℕ → ℝ) :
    p.law.expect (fun q => f q.val) =
      (swapped p).law.expect (fun q => f q.val) := by
  rw [expect_eq_extended_sum, expect_eq_extended_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [extendedWeight_swapped]

private theorem expect_one_add_pow_le (p : HypergeomParams) {u : ℝ} (hu : 0 ≤ u) :
    p.law.expect (fun q => (1 + u) ^ q.val) ≤
      (1 + ((p.draws : ℝ) / p.population) * u) ^ p.marked := by
  calc
    p.law.expect (fun q => (1 + u) ^ q.val) =
        p.law.expect (fun q => ∑ r ∈ Finset.range (p.population + 1),
          (q.val.choose r : ℝ) * u ^ r) := by
      congr 1
      funext q
      exact binomial_sum_extended (le_trans (Nat.le_of_lt_succ q.isLt) p.draws_le) u
    _ = ∑ r ∈ Finset.range (p.population + 1),
        p.law.expect (fun q => (q.val.choose r : ℝ)) * u ^ r := by
      unfold FiniteLaw.expect
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ ∑ r ∈ Finset.range (p.population + 1),
        (p.marked.choose r : ℝ) * (((p.draws : ℝ) / p.population) * u) ^ r := by
      apply Finset.sum_le_sum
      intro r _
      rw [p.expect_choose, mul_pow]
      have hratio := descFactorial_ratio_le_pow p.draws_le r
      have hchoose : (0 : ℝ) ≤ p.marked.choose r := Nat.cast_nonneg _
      have hpow : 0 ≤ u ^ r := pow_nonneg hu _
      calc
        _ = (p.marked.choose r : ℝ) *
            ((p.draws.descFactorial r : ℝ) / (p.population.descFactorial r : ℝ)) * u ^ r := by ring
        _ ≤ (p.marked.choose r : ℝ) * ((p.draws : ℝ) / p.population) ^ r * u ^ r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hchoose) hpow
        _ = _ := by ring
    _ = _ := (binomial_sum_extended p.marked_le _).symm

private theorem expect_one_add_pow_le_draws (p : HypergeomParams) {u : ℝ} (hu : 0 ≤ u) :
    p.law.expect (fun q => (1 + u) ^ q.val) ≤
      (1 + ((p.marked : ℝ) / p.population) * u) ^ p.draws := by
  rw [expect_swapped]
  exact expect_one_add_pow_le (swapped p) hu

private def markedComplement (p : HypergeomParams) : HypergeomParams where
  population := p.population
  marked := p.population - p.marked
  draws := p.draws
  marked_le := Nat.sub_le _ _
  draws_le := p.draws_le

private theorem expect_markedComplement (p : HypergeomParams) (f : ℕ → ℝ) :
    (markedComplement p).law.expect (fun q => f q.val) =
      p.law.expect (fun q => f (p.draws - q.val)) := by
  unfold FiniteLaw.expect
  apply Fintype.sum_equiv Fin.revPerm
  intro q
  have hq : q.val ≤ p.draws := Nat.le_of_lt_succ q.isLt
  simp [law_mass, weight, markedComplement, Fin.val_rev,
    Nat.sub_sub_self p.marked_le, Nat.sub_sub_self hq, mul_comm]

/-- H7: the exact transform comparison, including an empty population. -/
theorem expect_pow_le (p : HypergeomParams) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    p.law.expect (fun q => s ^ q.val) ≤
      (1 - (p.draws : ℝ) / p.population + ((p.draws : ℝ) / p.population) * s) ^
        p.marked := by
  by_cases hN : p.population = 0
  · have hK : p.marked = 0 := Nat.eq_zero_of_le_zero (hN ▸ p.marked_le)
    have hm : p.draws = 0 := Nat.eq_zero_of_le_zero (hN ▸ p.draws_le)
    have hfun : (fun q : Fin (p.draws + 1) => s ^ q.val) = (fun _ => (1 : ℝ)) := by
      funext q
      have hq : q.val = 0 := by have := q.isLt; omega
      simp [hq]
    rw [hfun, p.law.expect_const, hK, pow_zero]
  · have hNr : (p.population : ℝ) ≠ 0 := by exact_mod_cast hN
    have hu : 0 ≤ 1 / s - 1 := by
      apply sub_nonneg.mpr
      exact (le_div_iff₀ hs).2 (by simpa using hs1)
    let c := markedComplement (swapped p)
    have hcompare : c.law.expect (fun q => (1 / s) ^ q.val) ≤
        (1 + (((p.population - p.draws : ℕ) : ℝ) / p.population) * (1 / s - 1)) ^
          p.marked := by
      have h := expect_one_add_pow_le_draws c hu
      simpa [c, markedComplement, swapped] using h
    have htransform : p.law.expect (fun q => s ^ q.val) =
        s ^ p.marked * c.law.expect (fun q => (1 / s) ^ q.val) := by
      rw [expect_swapped]
      dsimp only [c]
      rw [expect_markedComplement, ← FiniteLaw.expect_const_mul]
      congr 1
      funext q
      have hq : q.val ≤ p.marked := Nat.le_of_lt_succ q.isLt
      have hpow : s ^ p.marked = s ^ q.val * s ^ (p.marked - q.val) := by
        rw [← pow_add, Nat.add_sub_of_le hq]
      change s ^ q.val = s ^ p.marked * (1 / s) ^ (p.marked - q.val)
      rw [hpow, div_pow, one_pow]
      field_simp
    rw [htransform]
    calc
      _ ≤ s ^ p.marked *
          (1 + (((p.population - p.draws : ℕ) : ℝ) / p.population) * (1 / s - 1)) ^
            p.marked := mul_le_mul_of_nonneg_left hcompare (pow_nonneg hs.le _)
      _ = _ := by
        rw [← mul_pow]
        congr 1
        rw [Nat.cast_sub p.draws_le]
        field_simp
        ring

private theorem expect_exp_le (p : HypergeomParams) (z : ℝ) :
    p.law.expect (fun q => Real.exp (z * (q.val : ℝ))) ≤
      Real.exp (p.mean * (Real.exp z - 1)) := by
  have hp0 : 0 ≤ (p.draws : ℝ) / p.population := by positivity
  have hp1 : (p.draws : ℝ) / p.population ≤ 1 := by
    by_cases hN : p.population = 0
    · simp [hN]
    · have hNpos : (0 : ℝ) < p.population := by
        exact_mod_cast Nat.pos_of_ne_zero hN
      apply (div_le_one hNpos).2
      exact_mod_cast p.draws_le
  have hpow : p.law.expect (fun q => (Real.exp z) ^ q.val) ≤
      (1 + ((p.draws : ℝ) / p.population) * (Real.exp z - 1)) ^ p.marked := by
    by_cases hz : 0 ≤ z
    · have h := expect_one_add_pow_le p (sub_nonneg.mpr (Real.one_le_exp hz))
      simpa using h
    · have h := p.expect_pow_le (Real.exp_pos z)
        (Real.exp_le_one_iff.mpr (le_of_lt (lt_of_not_ge hz)))
      calc
        _ ≤ _ := h
        _ = _ := by congr 1; ring
  have hbase : 0 ≤ 1 + ((p.draws : ℝ) / p.population) * (Real.exp z - 1) := by
    nlinarith [mul_nonneg hp0 (Real.exp_nonneg z)]
  calc
    _ = p.law.expect (fun q => (Real.exp z) ^ q.val) := by
      congr 1
      funext q
      rw [mul_comm, Real.exp_nat_mul]
    _ ≤ _ := hpow
    _ ≤ (Real.exp (((p.draws : ℝ) / p.population) * (Real.exp z - 1))) ^ p.marked := by
      apply pow_le_pow_left₀ hbase
      linarith [Real.add_one_le_exp (((p.draws : ℝ) / p.population) * (Real.exp z - 1))]
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      unfold mean
      ring

private theorem expect_centered_exp_le (p : HypergeomParams) {z : ℝ} (hz : |z| ≤ 1) :
    p.law.expect (fun q => Real.exp (z * ((q.val : ℝ) - p.mean))) ≤
      Real.exp (p.mean * z ^ 2) := by
  have hrem : Real.exp z - 1 - z ≤ z ^ 2 :=
    le_trans (le_abs_self _) (Real.abs_exp_sub_one_sub_id_le hz)
  calc
    _ = Real.exp (-z * p.mean) * p.law.expect (fun q => Real.exp (z * (q.val : ℝ))) := by
      rw [← FiniteLaw.expect_const_mul]
      congr 1
      funext q
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-z * p.mean) * Real.exp (p.mean * (Real.exp z - 1)) :=
      mul_le_mul_of_nonneg_left (expect_exp_le p z) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      calc
        _ = p.mean * (Real.exp z - 1 - z) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hrem p.mean_nonneg

private theorem chernoff_exponent {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 < t) :
    μ * (t / (2 * (μ + t))) ^ 2 - (t / (2 * (μ + t))) * t ≤
      -(1 / 4 : ℝ) * (t ^ 2 / (μ + t)) := by
  have hden : μ + t ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hμ ht)
  calc
    _ ≤ (μ + t) * (t / (2 * (μ + t))) ^ 2 - (t / (2 * (μ + t))) * t := by
      apply sub_le_sub_right
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ht.le) (sq_nonneg _)
    _ = _ := by field_simp; ring

private theorem concentration_quarter (p : HypergeomParams) {t : ℝ} (ht : 0 ≤ t) :
    p.law.prob (fun q => t ≤ |(q.val : ℝ) - p.mean|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (t ^ 2 / (p.mean + t)) t) := by
  by_cases ht0 : t = 0
  · subst t
    simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let z := t / (2 * (p.mean + t))
    have hden : 0 < 2 * (p.mean + t) :=
      mul_pos (by norm_num) (add_pos_of_nonneg_of_pos p.mean_nonneg htpos)
    have hzpos : 0 < z := div_pos htpos hden
    have hz1 : z ≤ 1 := by
      apply (div_le_one hden).2
      linarith [p.mean_nonneg]
    have hzabs : |z| ≤ 1 := by rwa [abs_of_pos hzpos]
    have hupper : p.law.prob (fun q => t ≤ (q.val : ℝ) - p.mean) ≤
        Real.exp (-(1 / 4 : ℝ) * (t ^ 2 / (p.mean + t))) := by
      calc
        _ ≤ p.law.prob (fun q => Real.exp (z * t) ≤
            Real.exp (z * ((q.val : ℝ) - p.mean))) := by
          apply p.law.prob_mono
          intro q hq
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq hzpos.le)
        _ ≤ p.law.expect (fun q => Real.exp (z * ((q.val : ℝ) - p.mean))) /
            Real.exp (z * t) :=
          p.law.markov (fun _ => Real.exp_nonneg _) (Real.exp_pos _)
        _ ≤ Real.exp (p.mean * z ^ 2) / Real.exp (z * t) :=
          div_le_div_of_nonneg_right (expect_centered_exp_le p hzabs) (Real.exp_nonneg _)
        _ = Real.exp (p.mean * z ^ 2 - z * t) := (Real.exp_sub _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (chernoff_exponent p.mean_nonneg htpos)
    have hlower : p.law.prob (fun q => t ≤ -((q.val : ℝ) - p.mean)) ≤
        Real.exp (-(1 / 4 : ℝ) * (t ^ 2 / (p.mean + t))) := by
      have hnegabs : |-z| ≤ 1 := by simpa only [abs_neg] using hzabs
      have hmgf : p.law.expect (fun q => Real.exp (-z * ((q.val : ℝ) - p.mean))) ≤
          Real.exp (p.mean * z ^ 2) := by
        simpa only [neg_sq] using expect_centered_exp_le p hnegabs
      calc
        _ ≤ p.law.prob (fun q => Real.exp (z * t) ≤
            Real.exp (-z * ((q.val : ℝ) - p.mean))) := by
          apply p.law.prob_mono
          intro q hq
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hq hzpos.le]
        _ ≤ p.law.expect (fun q => Real.exp (-z * ((q.val : ℝ) - p.mean))) /
            Real.exp (z * t) :=
          p.law.markov (fun _ => Real.exp_nonneg _) (Real.exp_pos _)
        _ ≤ Real.exp (p.mean * z ^ 2) / Real.exp (z * t) :=
          div_le_div_of_nonneg_right hmgf (Real.exp_nonneg _)
        _ = Real.exp (p.mean * z ^ 2 - z * t) := (Real.exp_sub _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (chernoff_exponent p.mean_nonneg htpos)
    calc
      _ ≤ p.law.prob (fun q => t ≤ (q.val : ℝ) - p.mean ∨
          t ≤ -((q.val : ℝ) - p.mean)) := by
        apply p.law.prob_mono
        intro q hq
        exact le_abs.mp hq
      _ ≤ p.law.prob (fun q => t ≤ (q.val : ℝ) - p.mean) +
          p.law.prob (fun q => t ≤ -((q.val : ℝ) - p.mean)) := p.law.prob_union_le _ _
      _ ≤ Real.exp (-(1 / 4 : ℝ) * (t ^ 2 / (p.mean + t))) +
          Real.exp (-(1 / 4 : ℝ) * (t ^ 2 / (p.mean + t))) := add_le_add hupper hlower
      _ = 2 * Real.exp (-(1 / 4 : ℝ) * (t ^ 2 / (p.mean + t))) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        nlinarith [min_le_left (t ^ 2 / (p.mean + t)) t]

/-- H5: one absolute exponential concentration constant works for all feasible
parameters, including zero means, empty populations, and deterministic laws. -/
theorem exists_concentration_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : HypergeomParams) (t : ℝ), 0 ≤ t →
      p.law.prob (fun q => t ≤ |(q.val : ℝ) - p.mean|) ≤
        2 * Real.exp (-c * min (t ^ 2 / (p.mean + t)) t) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro p t ht
  exact concentration_quarter p ht

end HypergeomParams

end
end Shuffle
