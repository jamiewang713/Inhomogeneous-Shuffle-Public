/- LB02 source compatibility port of `lean/Shuffle/HypergeometricConcentration.lean`.
Original SHA-256: 156d6e9aa774c2e3498975acfb64d9622dfc6d923cfcd96db5a866c4592e5a14.
Original files and freeze records are unchanged. -/

import RiffleLowerV2.Thinning.Compat.HypergeometricMoments
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-!
Finite hypergeometric exponential transforms and concentration.
The exported targets in this file are governed by audit/FROZEN_CONTRACT.md.
-/

namespace RiffleLowerV2.Thinning.Compat

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
  change (∑ q : Fin (p.draws + 1), (markedComplement p).weight q * f q.val) =
    ∑ q : Fin (p.draws + 1), p.weight q * f (p.draws - q.val)
  apply Fintype.sum_equiv Fin.revPerm
  intro q
  have hq : q.val ≤ p.draws := Nat.le_of_lt_succ q.isLt
  change (markedComplement p).law.mass q * f q.val =
    p.law.mass (Fin.rev q) * f (p.draws - (Fin.rev q).val)
  have hrev : (Fin.rev q).val = p.draws - q.val := by
    change p.draws + 1 - (q.val + 1) = p.draws - q.val
    omega
  simp only [law, weight, markedComplement]
  rw [hrev]
  simp [Nat.sub_sub_self p.marked_le, Nat.sub_sub_self hq, mul_comm]

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

/-- All positive power parameters, with no upper bound on s. -/
theorem expect_pow_le_all (p : HypergeomParams) {s : ℝ} (hs : 0 < s) :
    p.law.expect (fun q => s ^ q.val) ≤
      (1 - (p.draws : ℝ) / p.population + ((p.draws : ℝ) / p.population) * s) ^
        p.marked := by
  by_cases hs1 : s ≤ 1
  · exact p.expect_pow_le hs hs1
  · have hu : 0 ≤ s - 1 := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hs1))
    have h := expect_one_add_pow_le p hu
    simpa only [show 1 + (s - 1) = s by ring,
      show 1 + (p.draws : ℝ) / p.population * (s - 1) =
        1 - (p.draws : ℝ) / p.population + ((p.draws : ℝ) / p.population) * s by ring] using h

end HypergeomParams
end
end RiffleLowerV2.Thinning.Compat
