import RiffleLowerV2.Witness.OneColumnBasic

noncomputable section
open scoped BigOperators NNReal
open Set
namespace RiffleLowerV2.Witness
open TimeProfile

theorem tiltedWeight_nonneg {k : ℕ} (p : Simplex k) (alpha : ℝ) (l : Fin k) :
    0 ≤ tiltedWeight p alpha l := by
  exact div_nonneg (Real.rpow_nonneg (prob_nonneg p l) alpha)
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (prob_nonneg p j) alpha)

theorem tiltedWeight_zero {k : ℕ} (p : Simplex k) {alpha : ℝ} (ha : 1 ≤ alpha)
    {l : Fin k} (hl : prob p l = 0) : tiltedWeight p alpha l = 0 := by
  simp [tiltedWeight, hl, Real.zero_rpow (by linarith : alpha ≠ 0)]

theorem tiltedWeight_pos {k : ℕ} (p : Simplex k) {alpha : ℝ} (ha : 1 ≤ alpha)
    {l : Fin k} (hl : 0 < prob p l) : 0 < tiltedWeight p alpha l :=
  div_pos (Real.rpow_pos_of_pos hl alpha) (powerSum_pos p ha)

theorem tiltedWeight_support {k : ℕ} (p : Simplex k) {alpha : ℝ} (ha : 1 ≤ alpha)
    {l : Fin k} (hl : 0 < tiltedWeight p alpha l) : 0 < prob p l := by
  by_contra hn
  have hp : prob p l = 0 := le_antisymm (le_of_not_gt hn) (prob_nonneg p l)
  rw [tiltedWeight_zero p ha hp] at hl
  exact (lt_irrefl _ hl)

theorem sum_tiltedWeight {k : ℕ} (p : Simplex k) {alpha : ℝ} (ha : 1 ≤ alpha) :
    ∑ l, tiltedWeight p alpha l = 1 := by
  simp only [tiltedWeight, ← Finset.sum_div]
  exact div_self (powerSum_pos p ha).ne'

theorem tiltedCost_eq_sum {k : ℕ} (p : Simplex k) {alpha : ℝ} (ha : 1 ≤ alpha) :
    tiltedCost p alpha = ∑ l, tiltedWeight p alpha l * digitCost (prob p l) := by
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : prob p l = 0
  · simp [hl, tiltedWeight_zero p ha hl]
  · simp [hl]

theorem entropy_eq_cost {k : ℕ} (p : Simplex k) :
    shannonEntropy (prob p) = ∑ l, prob p l * digitCost (prob p l) := by
  simp only [shannonEntropy, digitCost, one_div, Real.log_inv, mul_neg,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : prob p l = 0 <;> simp [hl]

theorem entropy_eq_gibbs {k : ℕ} (q : Fin k → ℝ) (hq : ∀ l, 0 ≤ q l)
    (hs : ∑ l, q l = 1) :
    shannonEntropy q = ∑ l, if 0 < q l then q l * Real.log ((∑ i, q i)/q l) else 0 := by
  rw [hs]
  simp only [shannonEntropy, ← Finset.sum_neg_distrib, one_div, Real.log_inv, mul_neg]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : q l = 0
  · simp [hl]
  · have hp : 0 < q l := lt_of_le_of_ne (hq l) (Ne.symm hl)
    simp [hl, hp]

theorem shannonEntropy_nonneg {k : ℕ} (p : Simplex k) :
    0 ≤ shannonEntropy (prob p) := by
  rw [entropy_eq_cost]
  apply Finset.sum_nonneg
  intro l _
  by_cases hl : prob p l = 0
  · simp [hl]
  · have hp := lt_of_le_of_ne (prob_nonneg p l) (Ne.symm hl)
    apply mul_nonneg (prob_nonneg p l)
    exact Real.log_nonneg ((one_le_div hp).mpr (prob_le_one p l))

theorem shannonEntropy_le_log {k : ℕ} (hk : 2 ≤ k) (p : Simplex k) :
    shannonEntropy (prob p) ≤ Real.log k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let q : Simplex k := ⟨(fun _ => 1/(k : ℝ)), (fun _ => (one_div_pos.mpr hkpos).le), by
    simp [hkpos.ne']⟩
  have hq (l : Fin k) : prob q l = 1/(k : ℝ) := rfl
  have hg := finite_gibbs q (prob p) (prob_nonneg p) (theta := 1) (by norm_num)
    (fun l _ => by rw [hq]; exact one_div_pos.mpr hkpos)
  have hz : powerSum q 1 = 1 := by simp [powerSum, Real.rpow_one, sum_prob]
  have hc : (∑ l, prob p l * digitCost (prob q l)) = Real.log k := by
    simp only [hq, digitCost, one_div, inv_inv, ← Finset.sum_mul, sum_prob, one_mul]
  rw [← entropy_eq_gibbs _ (prob_nonneg p) (sum_prob p), hz, hc] at hg
  simpa using hg

theorem tiltedEntropy_identity {k : ℕ} (p : Simplex k) {alpha : ℝ} (ha : 1 ≤ alpha) :
    tiltedEntropy p alpha = alpha * tiltedCost p alpha - psi p alpha := by
  have hz := powerSum_pos p ha
  have hterm (l : Fin k) :
      -(if tiltedWeight p alpha l = 0 then 0 else
        tiltedWeight p alpha l * Real.log (tiltedWeight p alpha l)) =
      alpha * (tiltedWeight p alpha l * digitCost (prob p l)) +
        tiltedWeight p alpha l * Real.log (powerSum p alpha) := by
    by_cases hl : prob p l = 0
    · simp [tiltedWeight_zero p ha hl]
    · have hp := lt_of_le_of_ne (prob_nonneg p l) (Ne.symm hl)
      have hq := tiltedWeight_pos p ha hp
      have hlog : Real.log (tiltedWeight p alpha l) =
          alpha * Real.log (prob p l) - Real.log (powerSum p alpha) := by
        rw [tiltedWeight, Real.log_div (Real.rpow_pos_of_pos hp alpha).ne' hz.ne',
          Real.log_rpow hp]
      simp only [if_neg hq.ne', hlog, digitCost, one_div, Real.log_inv]
      ring
  simp only [tiltedEntropy, shannonEntropy, ← Finset.sum_neg_distrib]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sum_tiltedWeight p ha,
    one_mul, ← tiltedCost_eq_sum p ha]
  simp [psi]

theorem tilted_gibbs {k : ℕ} (p : Simplex k) {alpha beta : ℝ}
    (ha : 1 ≤ alpha) (hb : 1 ≤ beta) :
    tiltedEntropy p alpha ≤ beta * tiltedCost p alpha - psi p beta := by
  have hg := finite_gibbs p (tiltedWeight p alpha) (tiltedWeight_nonneg p alpha) hb
    (fun _ => tiltedWeight_support p ha)
  rw [← entropy_eq_gibbs _ (tiltedWeight_nonneg p alpha) (sum_tiltedWeight p ha),
    sum_tiltedWeight p ha, one_mul, ← tiltedCost_eq_sum p ha] at hg
  simpa only [tiltedEntropy, psi, sub_neg_eq_add] using hg

theorem tiltedCost_antitone {k : ℕ} (p : Simplex k) {alpha beta : ℝ}
    (ha : 1 ≤ alpha) (hab : alpha ≤ beta) : tiltedCost p beta ≤ tiltedCost p alpha := by
  have hb : 1 ≤ beta := ha.trans hab
  rcases eq_or_lt_of_le hab with rfl | hab
  · exact le_rfl
  · have h1 := tilted_gibbs p ha hb
    have h2 := tilted_gibbs p hb ha
    rw [tiltedEntropy_identity p ha] at h1
    rw [tiltedEntropy_identity p hb] at h2
    nlinarith

theorem antitoneOn_tiltedCost {k : ℕ} (p : Simplex k) :
    AntitoneOn (tiltedCost p) (Icc (2 : ℝ) 4) := by
  intro a ha b _ hab
  exact tiltedCost_antitone p (by linarith [ha.1]) hab

theorem tiltedWeight_one {k : ℕ} (p : Simplex k) (l : Fin k) :
    tiltedWeight p 1 l = prob p l := by
  simp [tiltedWeight, powerSum, sum_prob]

theorem tiltedCost_one {k : ℕ} (p : Simplex k) :
    tiltedCost p 1 = shannonEntropy (prob p) := by
  rw [tiltedCost_eq_sum p (by norm_num), entropy_eq_cost]
  simp_rw [tiltedWeight_one]

theorem tiltedCost_nonneg {k : ℕ} (p : Simplex k) {alpha : ℝ} (_ha : 1 ≤ alpha) :
    0 ≤ tiltedCost p alpha := by
  apply Finset.sum_nonneg
  intro l _
  split_ifs with hl
  · exact le_rfl
  · have hp := lt_of_le_of_ne (prob_nonneg p l) (Ne.symm hl)
    exact mul_nonneg (tiltedWeight_nonneg p alpha l)
      (Real.log_nonneg ((one_le_div hp).mpr (prob_le_one p l)))

theorem tiltedCost_bounds {k : ℕ} (hk : 2 ≤ k) (p : Simplex k) {alpha : ℝ}
    (ha : alpha ∈ Icc (2 : ℝ) 4) :
    0 ≤ tiltedCost p alpha ∧ tiltedCost p alpha ≤ Real.log k := by
  have ha1 : 1 ≤ alpha := by linarith [ha.1]
  refine ⟨tiltedCost_nonneg p ha1, ?_⟩
  have ht := tiltedCost_antitone p (alpha := 1) (by norm_num) ha1
  rw [tiltedCost_one] at ht
  exact ht.trans (shannonEntropy_le_log hk p)

theorem tiltedEntropy_bounds {k : ℕ} (_hk : 2 ≤ k) (p : Simplex k) {alpha : ℝ}
    (ha : alpha ∈ Icc (2 : ℝ) 4) :
    0 ≤ tiltedEntropy p alpha ∧ tiltedEntropy p alpha ≤ tiltedCost p alpha := by
  have ha1 : 1 ≤ alpha := by linarith [ha.1]
  let q : Simplex k := ⟨tiltedWeight p alpha, tiltedWeight_nonneg p alpha,
    sum_tiltedWeight p ha1⟩
  refine ⟨shannonEntropy_nonneg q, ?_⟩
  have hg := tilted_gibbs p ha1 (beta := 1) (by norm_num)
  have hz : psi p 1 = 0 := by simp [psi, powerSum, sum_prob]
  simpa [hz] using hg

theorem maxCost_le_tiltedCost {k : ℕ} (p : Simplex k) {alpha : ℝ} (ha : 1 ≤ alpha) :
    maxCost p ≤ tiltedCost p alpha := by
  rw [tiltedCost_eq_sum p ha]
  calc
    maxCost p = ∑ l, tiltedWeight p alpha l * maxCost p := by
      rw [← Finset.sum_mul, sum_tiltedWeight p ha, one_mul]
    _ ≤ ∑ l, tiltedWeight p alpha l * digitCost (prob p l) := by
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : prob p l = 0
      · simp [tiltedWeight_zero p ha hl]
      · have hp := lt_of_le_of_ne (prob_nonneg p l) (Ne.symm hl)
        apply mul_le_mul_of_nonneg_left _ (tiltedWeight_nonneg p alpha l)
        simp only [maxCost, digitCost, one_div, Real.log_inv]
        exact neg_le_neg (Real.log_le_log hp (prob_le_pileMax p l))

theorem psi_sharp_bounds {k : ℕ} (hk : 2 ≤ k) (p : Simplex k) {alpha : ℝ}
    (ha : alpha ∈ Icc (2 : ℝ) 4) :
    0 ≤ psi p alpha ∧ psi p alpha ≤ (alpha-1)*Real.log k := by
  refine ⟨(psi_bounds hk p ha).1, ?_⟩
  have hg := finite_gibbs p (prob p) (prob_nonneg p) (theta := alpha)
    (by linarith [ha.1]) (fun _ hl => hl)
  rw [← entropy_eq_gibbs _ (prob_nonneg p) (sum_prob p), ← entropy_eq_cost,
    sum_prob, one_mul] at hg
  have hb := shannonEntropy_le_log hk p
  have hm := mul_le_mul_of_nonneg_left hb (by linarith [ha.1] : 0 ≤ alpha-1)
  dsimp [psi]
  nlinarith

theorem psi_two_le_maxCost {k : ℕ} (p : Simplex k) : psi p 2 ≤ 2*maxCost p := by
  obtain ⟨l, hl⟩ := exists_prob_pos p
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨l, Finset.mem_univ _⟩
  obtain ⟨m, _, hm⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun i : Fin k => (⟨prob p i, prob_nonneg p i⟩ : ℝ≥0))
  have hm' : pileMax p = prob p m := congrArg (fun z : ℝ≥0 => (z : ℝ)) hm
  have hp : 0 < prob p m := by rw [← hm']; exact pileMax_pos p
  have hterm : prob p m ^ (2 : ℝ) ≤ powerSum p 2 :=
    Finset.single_le_sum (fun i _ => Real.rpow_nonneg (prob_nonneg p i) 2)
      (Finset.mem_univ _)
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hp 2) hterm
  rw [Real.log_rpow hp] at hlog
  simpa [psi, maxCost, digitCost, hm', one_div, Real.log_inv] using neg_le_neg hlog

theorem psi_four_ge_two {k : ℕ} (p : Simplex k) : 2*psi p 2 ≤ psi p 4 := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (fun l _ => sq_nonneg (prob p l))
  have hz2 : powerSum p 2 = ∑ l, (prob p l)^2 := by
    simp [powerSum]
  have hz4 : powerSum p 4 = ∑ l, ((prob p l)^2)^2 := by
    unfold powerSum
    apply Finset.sum_congr rfl
    intro l _
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
    ring
  have hp : powerSum p 4 ≤ (powerSum p 2)^2 := by
    simpa only [hz2, hz4] using hs
  have hlog := Real.log_le_log (powerSum_pos p (by norm_num : (1 : ℝ) ≤ 4)) hp
  rw [Real.log_pow] at hlog
  norm_num at hlog
  dsimp [psi]
  nlinarith

theorem continuousOn_powerSum {k : ℕ} (p : Simplex k) :
    ContinuousOn (powerSum p) (Icc (2 : ℝ) 4) := by
  apply continuousOn_finsetSum
  intro l _
  exact continuousOn_const.rpow continuousOn_id (fun a ha => Or.inr (by linarith [ha.1]))

theorem continuousOn_psi {k : ℕ} (p : Simplex k) :
    ContinuousOn (psi p) (Icc (2 : ℝ) 4) := by
  exact ((continuousOn_powerSum p).log
    (fun a ha => (powerSum_pos p (by linarith [ha.1])).ne')).neg

theorem continuousOn_tiltedCost {k : ℕ} (p : Simplex k) :
    ContinuousOn (tiltedCost p) (Icc (2 : ℝ) 4) := by
  unfold tiltedCost
  apply continuousOn_finsetSum
  intro l _
  by_cases hl : prob p l = 0
  · simp only [hl, if_true]
    exact continuousOn_const
  · simp only [hl, if_false]
    have hw : ContinuousOn (fun a => tiltedWeight p a l) (Icc (2 : ℝ) 4) := by
      exact (continuousOn_const.rpow continuousOn_id
        (fun a ha => Or.inr (by change 0 < a; linarith [ha.1]))).div (continuousOn_powerSum p)
        (fun a ha => (powerSum_pos p (by linarith [ha.1])).ne')
    exact hw.mul continuousOn_const

theorem continuousOn_tiltedEntropy {k : ℕ} (p : Simplex k) :
    ContinuousOn (tiltedEntropy p) (Icc (2 : ℝ) 4) := by
  apply ((continuousOn_id.mul (continuousOn_tiltedCost p)).sub (continuousOn_psi p)).congr
  intro a ha
  exact tiltedEntropy_identity p (by linarith [ha.1])

theorem oneColumnTilt : Targets.OneColumnTiltTarget := by
  intro k hk p
  refine ⟨continuousOn_tiltedCost p, antitoneOn_tiltedCost p,
    continuousOn_tiltedEntropy p, continuousOn_psi p, ?_, psi_two_le_maxCost p,
    psi_four_ge_two p⟩
  intro a ha
  exact ⟨(tiltedEntropy_bounds hk p ha).1, (tiltedEntropy_bounds hk p ha).2,
    (tiltedCost_bounds hk p ha).2, maxCost_le_tiltedCost p (by linarith [ha.1]),
    (psi_sharp_bounds hk p ha).1, (psi_sharp_bounds hk p ha).2,
    tiltedEntropy_identity p (by linarith [ha.1])⟩

end RiffleLowerV2.Witness
