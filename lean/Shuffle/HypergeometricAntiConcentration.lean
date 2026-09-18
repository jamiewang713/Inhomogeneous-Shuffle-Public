import Shuffle.HypergeometricMoments

/-! Point-mass anti-concentration from the hypergeometric birth/death identity. -/

noncomputable section
open scoped BigOperators

namespace Shuffle
namespace HypergeomParams

open Finset

private def birth (p : HypergeomParams) (x : ℝ) : ℝ :=
  ((p.marked : ℝ) - x) * ((p.draws : ℝ) - x) / (p.population : ℝ)

private def death (p : HypergeomParams) (x : ℝ) : ℝ :=
  x * ((p.population : ℝ) - (p.marked : ℝ) - (p.draws : ℝ) + x) /
    (p.population : ℝ)

private theorem cast_choose_step (n k : ℕ) :
    (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (n.choose k : ℝ) * ((n : ℝ) - (k : ℝ)) := by
  by_cases hkn : k ≤ n
  · have h := Nat.choose_succ_right_eq n k
    exact_mod_cast h
  · have hnk : n < k := by omega
    rw [Nat.choose_eq_zero_of_lt hnk, Nat.choose_eq_zero_of_lt (show n < k + 1 by omega)]
    simp

private theorem pointMass_nonneg (p : HypergeomParams) (q : ℕ) :
    0 ≤ p.pointMass q := p.law.prob_nonneg _

private theorem pointMass_formula (p : HypergeomParams) (q : ℕ) (hq : q ≤ p.draws) :
    p.pointMass q = (p.marked.choose q : ℝ) *
      ((p.population - p.marked).choose (p.draws - q) : ℝ) /
      (p.population.choose p.draws : ℝ) := by
  exact p.pointMass_eq_weight ⟨q, by omega⟩

private theorem detailed_balance (p : HypergeomParams) (q : ℕ) :
    birth p q * p.pointMass q = death p (q + 1) * p.pointMass (q + 1) := by
  by_cases hqm : q < p.draws
  · rw [pointMass_formula p q (by omega), pointMass_formula p (q + 1) (by omega)]
    have hK := cast_choose_step p.marked q
    have hU := cast_choose_step (p.population - p.marked) (p.draws - (q + 1))
    have hcastU : ((p.population - p.marked : ℕ) : ℝ) =
        (p.population : ℝ) - (p.marked : ℝ) := Nat.cast_sub p.marked_le
    have hsub : p.draws - (q + 1) + 1 = p.draws - q := by omega
    have hcastsub : ((p.draws - (q + 1) : ℕ) : ℝ) =
        (p.draws : ℝ) - ((q : ℝ) + 1) := by
      rw [Nat.cast_sub (show q + 1 ≤ p.draws by omega), Nat.cast_add, Nat.cast_one]
    rw [hsub, hcastU, hcastsub] at hU
    unfold birth death
    have hU' : ((p.population - p.marked).choose (p.draws - q) : ℝ) *
        ((p.draws : ℝ) - (q : ℝ)) =
      ((p.population - p.marked).choose (p.draws - (q + 1)) : ℝ) *
        ((p.population : ℝ) - (p.marked : ℝ) - (p.draws : ℝ) + (q : ℝ) + 1) := by
      nlinarith [hU]
    calc
      ((p.marked : ℝ) - q) * ((p.draws : ℝ) - q) / (p.population : ℝ) *
          ((p.marked.choose q : ℝ) *
            ((p.population - p.marked).choose (p.draws - q) : ℝ) /
              (p.population.choose p.draws : ℝ)) =
        ((p.marked.choose q : ℝ) * ((p.marked : ℝ) - q)) *
          (((p.population - p.marked).choose (p.draws - q) : ℝ) *
            ((p.draws : ℝ) - q)) /
          ((p.population : ℝ) * (p.population.choose p.draws : ℝ)) := by ring
      _ = ((p.marked.choose (q + 1) : ℝ) * ((q : ℝ) + 1)) *
          (((p.population - p.marked).choose (p.draws - (q + 1)) : ℝ) *
            ((p.population : ℝ) - p.marked - p.draws + q + 1)) /
          ((p.population : ℝ) * (p.population.choose p.draws : ℝ)) := by
        rw [← hK, hU']
      _ = _ := by ring
  · have hmq : p.draws ≤ q := by omega
    rw [p.pointMass_eq_zero_of_lt (show p.draws < q + 1 by omega), mul_zero]
    by_cases hq : q = p.draws
    · simp [birth, hq]
    · rw [p.pointMass_eq_zero_of_lt (show p.draws < q by omega), mul_zero]

private theorem rate_difference (p : HypergeomParams) (hN : (p.population : ℝ) ≠ 0)
    (x : ℝ) : death p x - birth p x = x - p.mean := by
  unfold death birth mean
  field_simp
  ring

private theorem stein_partial_sum (p : HypergeomParams) (hN : (p.population : ℝ) ≠ 0)
    (q : ℕ) :
    birth p q * p.pointMass q =
      ∑ j ∈ range (q + 1), (p.mean - (j : ℝ)) * p.pointMass j := by
  induction q with
  | zero => simp [birth, mean]
  | succ q ih =>
    rw [sum_range_succ, ← ih, detailed_balance p q]
    have hdiff := rate_difference p hN ((q : ℝ) + 1)
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith [congrArg (fun x : ℝ => x * p.pointMass (q + 1)) hdiff]

private theorem expect_abs_deviation_le (p : HypergeomParams) :
    p.law.expect (fun q => |(q.val : ℝ) - p.mean|) ≤ Real.sqrt p.varianceFormula := by
  have hv := p.law.variance_nonneg (fun q => |(q.val : ℝ) - p.mean|)
  rw [FiniteLaw.variance_eq] at hv
  have hs : p.law.expect (fun q => |(q.val : ℝ) - p.mean| ^ 2) = p.varianceFormula := by
    simp_rw [sq_abs]
    rw [← p.variance_val]
    unfold FiniteLaw.variance
    rw [p.expect_val]
  rw [hs] at hv
  exact Real.le_sqrt_of_sq_le (by linarith)

private theorem stein_le_sqrt (p : HypergeomParams) (hN : (p.population : ℝ) ≠ 0)
    (q : ℕ) (hqm : q ≤ p.draws) :
    birth p q * p.pointMass q ≤ Real.sqrt p.varianceFormula := by
  rw [stein_partial_sum p hN q]
  apply le_trans _ (expect_abs_deviation_le p)
  calc
    (∑ j ∈ range (q + 1), (p.mean - (j : ℝ)) * p.pointMass j) ≤
        ∑ j ∈ range (q + 1), |(j : ℝ) - p.mean| * p.pointMass j := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (pointMass_nonneg p j)
      simpa only [neg_sub] using neg_le_abs ((j : ℝ) - p.mean)
    _ ≤ ∑ j ∈ range (p.draws + 1), |(j : ℝ) - p.mean| * p.pointMass j := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      intro j hj hnot
      exact mul_nonneg (abs_nonneg _) (pointMass_nonneg p j)
    _ = p.law.expect (fun q => |(q.val : ℝ) - p.mean|) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
        |(j : ℝ) - p.mean| * p.pointMass j) (p.draws + 1)]
      unfold FiniteLaw.expect
      apply sum_congr rfl
      intro j hj
      rw [p.pointMass_eq_weight, p.law_mass]
      ring

private theorem exists_positive_mode (p : HypergeomParams) :
    ∃ q : Fin (p.draws + 1), 0 < p.weight q ∧ ∀ j, p.weight j ≤ p.weight q := by
  obtain ⟨q, hq, hmax⟩ := exists_max_image univ p.weight univ_nonempty
  have hm : ∀ j, p.weight j ≤ p.weight q := fun j => hmax j (mem_univ j)
  refine ⟨q, ?_, hm⟩
  by_contra h
  have hs : ∑ j, p.weight j ≤ ∑ _j : Fin (p.draws + 1), (0 : ℝ) := by
    apply sum_le_sum
    intro j hj
    exact (hm j).trans (le_of_not_gt h)
  rw [p.weight_sum] at hs
  simp at hs
  linarith

private theorem mean_le_marked (p : HypergeomParams) (hN : 0 < (p.population : ℝ)) :
    p.mean ≤ (p.marked : ℝ) := by
  unfold mean
  apply (div_le_iff₀ hN).2
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast p.draws_le) (Nat.cast_nonneg _)

private theorem mean_le_draws (p : HypergeomParams) (hN : 0 < (p.population : ℝ)) :
    p.mean ≤ (p.draws : ℝ) := by
  unfold mean
  apply (div_le_iff₀ hN).2
  nlinarith [mul_le_mul_of_nonneg_right
    (show (p.marked : ℝ) ≤ (p.population : ℝ) by exact_mod_cast p.marked_le)
    (show 0 ≤ (p.draws : ℝ) by positivity)]

private theorem mode_le_mean_add_two (p : HypergeomParams)
    (hN : 0 < (p.population : ℝ)) (q : Fin (p.draws + 1))
    (hpos : 0 < p.weight q) (hmax : ∀ j, p.weight j ≤ p.weight q) :
    (q.val : ℝ) ≤ p.mean + 2 := by
  have hqK : q.val ≤ p.marked := (p.weight_pos_iff q).mp hpos |>.1
  have hqm : q.val ≤ p.draws := by omega
  have hqKr : (q.val : ℝ) ≤ (p.marked : ℝ) := by exact_mod_cast hqK
  have hqmr : (q.val : ℝ) ≤ (p.draws : ℝ) := by exact_mod_cast hqm
  by_cases hq0 : q.val = 0
  · simp only [hq0, Nat.cast_zero]
    linarith [p.mean_nonneg]
  · let j : Fin (p.draws + 1) := ⟨q.val - 1, by omega⟩
    have hprev : ((q.val - 1 : ℕ) : ℝ) = (q.val : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ q.val by omega), Nat.cast_one]
    have hsucc : q.val - 1 + 1 = q.val := by omega
    have hbalance := detailed_balance p (q.val - 1)
    rw [hsucc, p.pointMass_eq_weight q, p.pointMass_eq_weight j, hprev] at hbalance
    have hcancel : (q.val : ℝ) - 1 + 1 = (q.val : ℝ) := by ring
    rw [hcancel] at hbalance
    have hbnonneg : 0 ≤ birth p ((q.val : ℝ) - 1) := by
      unfold birth
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hN.le
    have hmul : death p q.val * p.weight q ≤
        birth p ((q.val : ℝ) - 1) * p.weight q := by
      rw [← hbalance]
      exact mul_le_mul_of_nonneg_left (hmax j) hbnonneg
    have hrates : death p q.val ≤ birth p ((q.val : ℝ) - 1) :=
      (mul_le_mul_right hpos).mp hmul
    unfold death birth at hrates
    have hrates' := (div_le_div_iff_of_pos_right hN).mp hrates
    have hmeanN : p.mean * (p.population : ℝ) = (p.marked : ℝ) * p.draws := by
      unfold mean
      exact div_mul_cancel₀ _ hN.ne'
    have hKN : (p.marked : ℝ) ≤ (p.population : ℝ) := by exact_mod_cast p.marked_le
    have hmN : (p.draws : ℝ) ≤ (p.population : ℝ) := by exact_mod_cast p.draws_le
    nlinarith only [hrates', hmeanN, hKN, hmN, hN, p.mean_nonneg]

private theorem birth_lower_of_mode (p : HypergeomParams)
    (hN : 0 < (p.population : ℝ)) (q : Fin (p.draws + 1))
    (hpos : 0 < p.weight q) (hmax : ∀ j, p.weight j ≤ p.weight q) :
    birth p p.mean - 4 ≤ birth p q.val := by
  have hqK : (q.val : ℝ) ≤ (p.marked : ℝ) := by
    exact_mod_cast ((p.weight_pos_iff q).mp hpos).1
  have hqm : (q.val : ℝ) ≤ (p.draws : ℝ) := by exact_mod_cast (show q.val ≤ p.draws by omega)
  have hupper := mode_le_mean_add_two p hN q hpos hmax
  have hcoeff0 : 0 ≤ (p.marked : ℝ) + p.draws - q.val - p.mean := by
    linarith [mean_le_draws p hN]
  have hcoeff2 : (p.marked : ℝ) + p.draws - q.val - p.mean ≤
      2 * (p.population : ℝ) := by
    have hKN : (p.marked : ℝ) ≤ (p.population : ℝ) := by exact_mod_cast p.marked_le
    have hmN : (p.draws : ℝ) ≤ (p.population : ℝ) := by exact_mod_cast p.draws_le
    linarith [p.mean_nonneg, show 0 ≤ (q.val : ℝ) by positivity]
  have hprod : ((q.val : ℝ) - p.mean) *
      ((p.marked : ℝ) + p.draws - q.val - p.mean) ≤ 4 * (p.population : ℝ) := by
    calc
      _ ≤ 2 * ((p.marked : ℝ) + p.draws - q.val - p.mean) :=
        mul_le_mul_of_nonneg_right (by linarith) hcoeff0
      _ ≤ _ := by linarith
  have hnum : ((p.marked : ℝ) - p.mean) * ((p.draws : ℝ) - p.mean) -
      4 * (p.population : ℝ) ≤
      ((p.marked : ℝ) - q.val) * ((p.draws : ℝ) - q.val) := by
    nlinarith only [hprod]
  unfold birth
  calc
    ((p.marked : ℝ) - p.mean) * ((p.draws : ℝ) - p.mean) / (p.population : ℝ) - 4 =
        (((p.marked : ℝ) - p.mean) * ((p.draws : ℝ) - p.mean) -
          4 * (p.population : ℝ)) / (p.population : ℝ) := by
      field_simp
      ring
    _ ≤ _ := (div_le_div_iff_of_pos_right hN).mpr hnum

private theorem birth_mean_ge_half_variance (p : HypergeomParams)
    (hN : (2 : ℝ) ≤ (p.population : ℝ)) (hv : 0 ≤ p.varianceFormula) :
    p.varianceFormula / 2 ≤ birth p p.mean := by
  have hn : (p.population : ℝ) ≠ 0 := by linarith
  have hn1 : (p.population : ℝ) - 1 ≠ 0 := by linarith
  have hidentity : birth p p.mean * (p.population : ℝ) =
      p.varianceFormula * ((p.population : ℝ) - 1) := by
    unfold birth mean varianceFormula
    field_simp
    ring
  have hprod : 0 ≤ p.varianceFormula * ((p.population : ℝ) - 2) :=
    mul_nonneg hv (by linarith)
  nlinarith only [hN, hidentity, hprod]

/-- A uniform point-mass bound for every positive-variance hypergeometric law. -/
theorem pointMass_le_four_div_sqrt (p : HypergeomParams) (hv : 0 < p.varianceFormula)
    (k : ℕ) : p.pointMass k ≤ 4 / Real.sqrt p.varianceFormula := by
  have hs : 0 < Real.sqrt p.varianceFormula := Real.sqrt_pos.mpr hv
  have hs2 : (Real.sqrt p.varianceFormula) ^ 2 = p.varianceFormula := Real.sq_sqrt hv.le
  by_cases hlarge : 16 ≤ p.varianceFormula
  · have hNnat : 2 ≤ p.population := by
      by_contra h
      have hzero := p.variance_eq_zero_of_population_le_one (by omega)
      rw [p.variance_val] at hzero
      linarith
    have hNreal : (2 : ℝ) ≤ (p.population : ℝ) := by exact_mod_cast hNnat
    have hN : 0 < (p.population : ℝ) := by linarith
    obtain ⟨q, hpos, hmax⟩ := exists_positive_mode p
    have hb : p.varianceFormula / 4 ≤ birth p q.val := by
      have h₁ := birth_lower_of_mode p hN q hpos hmax
      have h₂ := birth_mean_ge_half_variance p hNreal hv.le
      linarith
    have hstein := stein_le_sqrt p hN.ne' q.val (by omega)
    rw [p.pointMass_eq_weight] at hstein
    have hmode : p.weight q ≤ 4 / Real.sqrt p.varianceFormula := by
      apply (le_div_iff₀ hs).mpr
      apply (mul_le_mul_right hs).mp
      calc
        p.weight q * Real.sqrt p.varianceFormula * Real.sqrt p.varianceFormula =
            p.weight q * p.varianceFormula := by
          rw [mul_assoc, ← pow_two, hs2]
        _ ≤ 4 * Real.sqrt p.varianceFormula := by
          nlinarith [mul_le_mul_of_nonneg_right hb hpos.le]
    by_cases hkm : k ≤ p.draws
    · let j : Fin (p.draws + 1) := ⟨k, by omega⟩
      rw [p.pointMass_eq_weight j]
      exact (hmax j).trans hmode
    · rw [p.pointMass_eq_zero_of_lt (by omega)]
      positivity
  · have hsle : Real.sqrt p.varianceFormula ≤ 4 := by nlinarith [hs2, hs.le]
    calc
      p.pointMass k ≤ 1 := p.pointMass_le_one k
      _ ≤ 4 / Real.sqrt p.varianceFormula := (le_div_iff₀ hs).mpr (by linarith)

/-- Frozen H6: the same absolute constant works for every feasible parameter. -/
theorem exists_pointMass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ p : HypergeomParams, 0 < p.varianceFormula →
      ∀ q : ℕ, p.pointMass q ≤ C / Real.sqrt p.varianceFormula := by
  exact ⟨4, by norm_num, fun p hv q => p.pointMass_le_four_div_sqrt hv q⟩

end HypergeomParams
end Shuffle
