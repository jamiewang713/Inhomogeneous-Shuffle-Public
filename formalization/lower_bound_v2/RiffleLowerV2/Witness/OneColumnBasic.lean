import Contracts.v1.WitnessGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2.Witness
open TimeProfile

-- Source ports: RiffleTimeProfile/Analysis.lean; see audit/LB05/one_column_provenance_v1.md.
theorem powerSum_pos {k : ℕ} (p : Simplex k) {theta : ℝ} (_htheta : 1 ≤ theta) :
    0 < powerSum p theta := by
  obtain ⟨l, hl⟩ := exists_prob_pos p
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hl theta)
    (Finset.single_le_sum (fun i _ => Real.rpow_nonneg (prob_nonneg p i) theta)
      (Finset.mem_univ l))

theorem powerSum_le_one {k : ℕ} (_hk : 2 ≤ k) (p : Simplex k) {theta : ℝ}
    (htheta : theta ∈ Icc (2 : ℝ) 4) :
    powerSum p theta ≤ 1 := by
  calc
    powerSum p theta ≤ ∑ l, prob p l := by
      exact Finset.sum_le_sum fun l _ =>
        Real.rpow_le_self_of_le_one (prob_nonneg p l) (prob_le_one p l)
          (by linarith [htheta.1])
    _ = 1 := sum_prob p

theorem maxCost_bounds {k : ℕ} (hk : 2 ≤ k) (p : Simplex k) :
    0 ≤ maxCost p ∧ maxCost p ≤ Real.log (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 < pileMax p := pileMax_pos p
  have hcard := inv_card_le_pileMax (by omega : 0 < k) p
  have hmul : 1 ≤ pileMax p * (k : ℝ) := (div_le_iff₀ hkpos).mp hcard
  have hinv : 1 / pileMax p ≤ (k : ℝ) := (div_le_iff₀ hp).mpr (by nlinarith)
  constructor
  · change 0 ≤ Real.log (1 / pileMax p)
    apply Real.log_nonneg
    exact (one_le_div hp).mpr (pileMax_le_one p)
  · exact Real.log_le_log (one_div_pos.mpr hp) hinv

theorem psi_bounds {k : ℕ} (hk : 2 ≤ k) (p : Simplex k)
    {theta : ℝ} (htheta : theta ∈ Icc (2 : ℝ) 4) :
    0 ≤ psi p theta ∧ psi p theta ≤ 4 * Real.log (k : ℝ) := by
  have ht : 1 ≤ theta := by linarith [htheta.1]
  have hz := powerSum_pos p ht
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hsum : (∑ _ : Fin k, (1 : ℝ) / k) ≤ ∑ l, prob p l := by
    simp [sum_prob, hkne]
  obtain ⟨l, _, hl⟩ := Finset.exists_le_of_sum_le hne hsum
  have hlpos : 0 < prob p l := lt_of_lt_of_le (one_div_pos.mpr hkpos) hl
  have hterm : prob p l ^ theta ≤ powerSum p theta :=
    Finset.single_le_sum (fun i _ => Real.rpow_nonneg (prob_nonneg p i) theta)
      (Finset.mem_univ l)
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hlpos theta) hterm
  rw [Real.log_rpow hlpos theta] at hlog
  have hinv : 1 / prob p l ≤ (k : ℝ) := (div_le_iff₀ hlpos).mpr
    (by have := (div_le_iff₀ hkpos).mp hl; nlinarith)
  have hcost : -Real.log (prob p l) ≤ Real.log (k : ℝ) := by
    simpa only [one_div, Real.log_inv] using
      Real.log_le_log (one_div_pos.mpr hlpos) hinv
  have hklog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hm := mul_le_mul_of_nonneg_left hcost (by linarith [htheta.1] : 0 ≤ theta)
  have htlog := mul_le_mul_of_nonneg_right htheta.2 hklog
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos hz.le (powerSum_le_one hk p htheta))
  · dsimp [psi]
    nlinarith

/- E01: the finite Gibbs inequality, with its zero-total branch included. -/
theorem finite_gibbs {k : ℕ} (p : Simplex k) (c : Fin k → ℝ)
    (hc : ∀ l, 0 ≤ c l) {theta : ℝ} (htheta : 1 ≤ theta)
    (hsupport : ∀ l, 0 < c l → 0 < prob p l) :
    (∑ l, if 0 < c l then c l * Real.log ((∑ i, c i) / c l) else 0) ≤
      theta * (∑ l, c l * digitCost (prob p l)) +
        (∑ l, c l) * Real.log (powerSum p theta) := by
  classical
  let C : ℝ := ∑ l, c l
  let Z : ℝ := powerSum p theta
  have hC : 0 ≤ C := Finset.sum_nonneg (fun l _ => hc l)
  have hZ : 0 < Z := powerSum_pos p htheta
  by_cases hCzero : C = 0
  · have hc_zero : ∀ l, c l = 0 := by
      intro l
      have hle : c l ≤ C := Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ l)
      exact le_antisymm (by simpa [hCzero] using hle) (hc l)
    simp [hc_zero]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hterm : ∀ l,
        (if 0 < c l then c l * Real.log (C / c l) else 0) ≤
          theta * (c l * digitCost (prob p l)) + c l * Real.log Z +
            C * (prob p l ^ theta) / Z - c l := by
      intro l
      by_cases hl : 0 < c l
      · have hp := hsupport l hl
        have hpPow := Real.rpow_pos_of_pos hp theta
        have hratio : 0 < C * (prob p l ^ theta) / (c l * Z) :=
          div_pos (mul_pos hCpos hpPow) (mul_pos hl hZ)
        have hlog : Real.log (C * (prob p l ^ theta) / (c l * Z)) =
            Real.log (C / c l) + theta * Real.log (prob p l) - Real.log Z := by
          rw [Real.log_div (ne_of_gt (mul_pos hCpos hpPow)) (ne_of_gt (mul_pos hl hZ)),
            Real.log_mul (ne_of_gt hCpos) (ne_of_gt hpPow),
            Real.log_mul (ne_of_gt hl) (ne_of_gt hZ),
            Real.log_div (ne_of_gt hCpos) (ne_of_gt hl), Real.log_rpow hp theta]
          ring
        have hineq := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio) (hc l)
        rw [hlog] at hineq
        have hcancel : c l * (C * (prob p l ^ theta) / (c l * Z) - 1) =
            C * (prob p l ^ theta) / Z - c l := by
          field_simp
        rw [hcancel] at hineq
        simp only [if_pos hl, digitCost, one_div, Real.log_inv]
        nlinarith
      · have hzero : c l = 0 := le_antisymm (le_of_not_gt hl) (hc l)
        simp only [hzero, lt_self_iff_false, if_false, zero_mul, mul_zero,
          zero_add, sub_zero]
        exact div_nonneg (mul_nonneg hC (Real.rpow_nonneg (prob_nonneg p l) theta)) hZ.le
    have hsum := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) => hterm l)
    have hsumPow : (∑ l, prob p l ^ theta) = Z := rfl
    have hcancelSum : (∑ l, C * (prob p l ^ theta) / Z) = C := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hsumPow, mul_div_cancel_right₀ _ (ne_of_gt hZ)]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul] at hsum
    rw [show (∑ l, C * (prob p l ^ theta) / Z) = C from hcancelSum] at hsum
    change (∑ l, if 0 < c l then c l * Real.log (C / c l) else 0) ≤
      theta * (∑ l, c l * digitCost (prob p l)) + C * Real.log Z
    dsimp [C] at hsum ⊢
    linarith


end RiffleLowerV2.Witness
