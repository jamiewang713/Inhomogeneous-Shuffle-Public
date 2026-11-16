/- LB02 source compatibility port of `lean/Shuffle/HypergeometricMoments.lean`.
Original SHA-256: c667d6024b8e6aadf26c917e4bc97dbc13f5efb570af0edfbecef4283117b109.
Original files and freeze records are unchanged. -/

import RiffleLowerV2.Thinning.Compat.Hypergeometric
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring

/-! Exact factorial moments of the finite hypergeometric law. -/

namespace RiffleLowerV2.Thinning.Compat

open Finset

private theorem choose_mul_descFactorial (n k r : ℕ) (hr : r ≤ k) :
    n.choose k * k.descFactorial r =
      n.descFactorial r * (n - r).choose (k - r) := by
  by_cases hk : k ≤ n
  · rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose]
    calc
      n.choose k * (r.factorial * k.choose r) =
          r.factorial * (n.choose k * k.choose r) := by ring
      _ = r.factorial * (n.choose r * (n - r).choose (k - r)) := by
        rw [Nat.choose_mul hr]
      _ = r.factorial * n.choose r * (n - r).choose (k - r) := by ring
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [Nat.choose_eq_zero_of_lt hnk, zero_mul]
    by_cases hrn : r ≤ n
    · rw [Nat.choose_eq_zero_of_lt (show n - r < k - r by omega), mul_zero]
    · rw [Nat.descFactorial_of_lt (Nat.lt_of_not_ge hrn), zero_mul]

private theorem weighted_choose_sum (K U m r : ℕ) (hrm : r ≤ m) :
    (∑ q ∈ range (m + 1),
      K.choose q * U.choose (m - q) * q.descFactorial r) =
      K.descFactorial r * (K - r + U).choose (m - r) := by
  have hsplit : m + 1 = r + (m - r + 1) := by omega
  rw [hsplit, sum_range_add]
  have hz : (∑ q ∈ range r,
      K.choose q * U.choose (m - q) * q.descFactorial r) = 0 := by
    apply sum_eq_zero
    intro q hq
    rw [Nat.descFactorial_of_lt (mem_range.mp hq), mul_zero]
  rw [hz, zero_add]
  calc
    (∑ q ∈ range (m - r + 1),
      K.choose (r + q) * U.choose (m - (r + q)) * (r + q).descFactorial r) =
        ∑ q ∈ range (m - r + 1),
          K.descFactorial r * ((K - r).choose q * U.choose (m - r - q)) := by
      apply sum_congr rfl
      intro q hq
      have hstep := choose_mul_descFactorial K (r + q) r (by omega)
      have hsub : r + q - r = q := by omega
      have hsub' : m - (r + q) = m - r - q := by omega
      rw [hsub] at hstep
      rw [hsub']
      calc
        K.choose (r + q) * U.choose (m - r - q) * (r + q).descFactorial r =
            (K.choose (r + q) * (r + q).descFactorial r) * U.choose (m - r - q) := by ring
        _ = K.descFactorial r * (K - r).choose q * U.choose (m - r - q) := by rw [hstep]
        _ = K.descFactorial r * ((K - r).choose q * U.choose (m - r - q)) := by ring
    _ = K.descFactorial r *
          ∑ q ∈ range (m - r + 1), (K - r).choose q * U.choose (m - r - q) := by
      rw [mul_sum]
    _ = K.descFactorial r * (K - r + U).choose (m - r) := by
      congr 1
      rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem raw_factorial_moment (N K m r : ℕ) (hKN : K ≤ N) (hmN : m ≤ N) :
    (∑ q : Fin (m + 1),
      ((K.choose q.val : ℝ) * ((N - K).choose (m - q.val) : ℝ) /
        (N.choose m : ℝ)) * (q.val.descFactorial r : ℝ)) =
      (K.descFactorial r : ℝ) * (m.descFactorial r : ℝ) /
        (N.descFactorial r : ℝ) := by
  have hchoose : (N.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmN).ne'
  by_cases hrm : r ≤ m
  · have hrN : r ≤ N := hrm.trans hmN
    have hdesc : (N.descFactorial r : ℝ) ≠ 0 := by
      exact_mod_cast (show N.descFactorial r ≠ 0 from
        fun h => (Nat.not_lt_of_ge hrN) (Nat.descFactorial_eq_zero_iff_lt.mp h))
    have hsumNat := weighted_choose_sum K (N - K) m r hrm
    have hsum : (∑ q ∈ range (m + 1),
        (K.choose q : ℝ) * ((N - K).choose (m - q) : ℝ) *
          (q.descFactorial r : ℝ)) =
        (K.descFactorial r : ℝ) * ((N - r).choose (m - r) : ℝ) := by
      by_cases hrK : r ≤ K
      · have hN : K - r + (N - K) = N - r := by omega
        rw [hN] at hsumNat
        exact_mod_cast hsumNat
      · have hKr : K.descFactorial r = 0 := Nat.descFactorial_of_lt (by omega)
        rw [hKr, zero_mul] at hsumNat
        rw [hKr, Nat.cast_zero, zero_mul]
        exact_mod_cast hsumNat
    have hratio : (N.choose m : ℝ) * (m.descFactorial r : ℝ) =
        (N.descFactorial r : ℝ) * ((N - r).choose (m - r) : ℝ) := by
      exact_mod_cast choose_mul_descFactorial N m r hrm
    rw [Fin.sum_univ_eq_sum_range (fun q : ℕ =>
      ((K.choose q : ℝ) * ((N - K).choose (m - q) : ℝ) /
        (N.choose m : ℝ)) * (q.descFactorial r : ℝ)) (m + 1)]
    calc
      (∑ q ∈ range (m + 1),
        ((K.choose q : ℝ) * ((N - K).choose (m - q) : ℝ) /
          (N.choose m : ℝ)) * (q.descFactorial r : ℝ)) =
          (∑ q ∈ range (m + 1),
            (K.choose q : ℝ) * ((N - K).choose (m - q) : ℝ) *
              (q.descFactorial r : ℝ)) / (N.choose m : ℝ) := by
        rw [sum_div]
        apply sum_congr rfl
        intro q hq
        ring
      _ = (K.descFactorial r : ℝ) * ((N - r).choose (m - r) : ℝ) /
          (N.choose m : ℝ) := by rw [hsum]
      _ = (K.descFactorial r : ℝ) * (m.descFactorial r : ℝ) /
          (N.descFactorial r : ℝ) := by
        apply (div_eq_div_iff hchoose hdesc).2
        nlinarith [hratio]
  · have hmr : m < r := by omega
    rw [Nat.descFactorial_of_lt hmr, Nat.cast_zero, mul_zero, zero_div]
    apply sum_eq_zero
    intro q hq
    rw [Nat.descFactorial_of_lt (show q.val < r by omega), Nat.cast_zero, mul_zero]

namespace HypergeomParams

/-- The exact descending-factorial moment, including order zero and all degenerate populations. -/
theorem expect_descFactorial (p : HypergeomParams) (r : ℕ) :
    p.law.expect (fun q => (q.val.descFactorial r : ℝ)) =
      (p.marked.descFactorial r : ℝ) * (p.draws.descFactorial r : ℝ) /
        (p.population.descFactorial r : ℝ) := by
  exact raw_factorial_moment p.population p.marked p.draws r p.marked_le p.draws_le

/-- The first moment is valid for the empty population as well. -/
theorem expect_val (p : HypergeomParams) :
    p.law.expect (fun q => (q.val : ℝ)) = p.mean := by
  simpa only [Nat.descFactorial_one, mean] using p.expect_descFactorial 1

/-- The binomial-coefficient form of the same factorial moment. -/
theorem expect_choose (p : HypergeomParams) (r : ℕ) :
    p.law.expect (fun q => (q.val.choose r : ℝ)) =
      (p.marked.choose r : ℝ) * (p.draws.descFactorial r : ℝ) /
        (p.population.descFactorial r : ℝ) := by
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have h := p.expect_descFactorial r
  have hfun : (fun q : Fin (p.draws + 1) => (q.val.descFactorial r : ℝ)) =
      fun q => (r.factorial : ℝ) * (q.val.choose r : ℝ) := by
    funext q
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose q.val r
  rw [hfun, p.law.expect_const_mul] at h
  apply mul_left_cancel₀ hf
  calc
    (r.factorial : ℝ) * p.law.expect (fun q => (q.val.choose r : ℝ)) =
        (p.marked.descFactorial r : ℝ) * (p.draws.descFactorial r : ℝ) /
          (p.population.descFactorial r : ℝ) := h
    _ = (r.factorial : ℝ) *
        ((p.marked.choose r : ℝ) * (p.draws.descFactorial r : ℝ) /
          (p.population.descFactorial r : ℝ)) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      ring

/-- The second factorial moment written with subtraction in the reals. -/
theorem expect_mul_pred (p : HypergeomParams) :
    p.law.expect (fun q => (q.val : ℝ) * ((q.val : ℝ) - 1)) =
      (p.marked : ℝ) * ((p.marked : ℝ) - 1) *
        ((p.draws : ℝ) * ((p.draws : ℝ) - 1)) /
        ((p.population : ℝ) * ((p.population : ℝ) - 1)) := by
  simpa only [Nat.cast_descFactorial_two] using p.expect_descFactorial 2

/-- The variance is exact, with no positive-population assumption. -/
theorem variance_val (p : HypergeomParams) :
    p.law.variance (fun q => (q.val : ℝ)) = p.varianceFormula := by
  have hsq : (fun q : Fin (p.draws + 1) => (q.val : ℝ) ^ 2) =
      fun q => (q.val : ℝ) * ((q.val : ℝ) - 1) + (q.val : ℝ) := by
    funext q
    ring
  rw [FiniteLaw.variance_eq, hsq, p.law.expect_add, p.expect_mul_pred, p.expect_val]
  unfold mean varianceFormula
  by_cases hN : p.population = 0
  · have hK : p.marked = 0 := by have := p.marked_le; omega
    have hm : p.draws = 0 := by have := p.draws_le; omega
    simp [hN, hK, hm]
  by_cases hN1 : p.population = 1
  · have hK : p.marked = 0 ∨ p.marked = 1 := by have := p.marked_le; omega
    have hm : p.draws = 0 ∨ p.draws = 1 := by have := p.draws_le; omega
    rcases hK with hK | hK <;> rcases hm with hm | hm <;> simp [hN1, hK, hm]
  · have hn : (p.population : ℝ) ≠ 0 := by exact_mod_cast hN
    have hn1 : (p.population : ℝ) - 1 ≠ 0 := by
      intro h
      apply hN1
      exact_mod_cast (sub_eq_zero.mp h)
    field_simp
    ring

/-- Exactly the four endpoint parameter cases have zero variance. -/
theorem variance_eq_zero_iff (p : HypergeomParams) :
    p.law.variance (fun q => (q.val : ℝ)) = 0 ↔
      p.marked = 0 ∨ p.draws = 0 ∨ p.marked = p.population ∨
        p.draws = p.population := by
  rw [p.variance_val]
  by_cases hN : p.population ≤ 1
  · have hcases : p.population = 0 ∨ p.population = 1 := by omega
    have hparam : p.marked = 0 ∨ p.draws = 0 ∨ p.marked = p.population ∨
        p.draws = p.population := by
      have := p.marked_le
      have := p.draws_le
      omega
    have hv : p.varianceFormula = 0 := by
      rcases hcases with hN0 | hN1
      · simp [varianceFormula, hN0]
      · simp [varianceFormula, hN1]
    exact ⟨fun _ => hparam, fun _ => hv⟩
  · have hn : (2 : ℝ) ≤ (p.population : ℝ) := by exact_mod_cast (show 2 ≤ p.population by omega)
    have hden : (p.population : ℝ) ^ 2 * ((p.population : ℝ) - 1) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero 2 (by linarith)) (by linarith)
    simp only [varianceFormula, div_eq_zero_iff, mul_eq_zero, Nat.cast_eq_zero,
      sub_eq_zero, Nat.cast_inj, hden, or_false]
    aesop

/-- Populations of size zero or one always give a deterministic count. -/
theorem variance_eq_zero_of_population_le_one (p : HypergeomParams)
    (hN : p.population ≤ 1) : p.law.variance (fun q => (q.val : ℝ)) = 0 := by
  apply p.variance_eq_zero_iff.mpr
  have := p.marked_le
  have := p.draws_le
  omega

end HypergeomParams

end RiffleLowerV2.Thinning.Compat
