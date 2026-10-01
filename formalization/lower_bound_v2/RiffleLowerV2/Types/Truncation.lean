import RiffleLowerV2.Shared.Geometry

noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2.Types
open TimeProfile
attribute [local instance] Classical.propDecidable

theorem exists_prob_ge_inv_card {k : ℕ} (hk : 0 < k) (p : Simplex k) :
    ∃ l : Fin k, 1 / (k : ℝ) ≤ prob p l := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hs : (∑ _ : Fin k, (1 : ℝ) / k) ≤ ∑ l, prob p l := by
    simp [sum_prob, ne_of_gt hkpos]
  obtain ⟨l, _, hl⟩ := Finset.exists_le_of_sum_le hne hs
  exact ⟨l, hl⟩

theorem cutoff_small {k : ℕ} (hk : 2 ≤ k) {xi : ℝ} (hxi : 0 < xi)
    (hxiK : xi < 1 / (4 * (k : ℝ))) :
    xi < 1/8 ∧ 2*xi < 1/(k : ℝ) ∧ 3*xi < 1/(k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h := (lt_div_iff₀ (by positivity : 0 < 4 * (k : ℝ))).mp hxiK
  have hxik : 0 < xi * (k : ℝ) := mul_pos hxi hkpos
  refine ⟨?_, (lt_div_iff₀ hkpos).mpr ?_, (lt_div_iff₀ hkpos).mpr ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hk2 hxi.le]
  · nlinarith
  · nlinarith

theorem cutoff_log_ge_one {xi : ℝ} (hxi : 0 < xi) (hsmall : xi < 1/8) :
    1 ≤ Real.log (1/xi) := by
  have hlog2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have heq : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2*2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    norm_num at hlog2
    linarith
  exact hlog4.trans (Real.log_le_log (by norm_num)
    ((le_div_iff₀ hxi).mpr (by linarith)))

def restrictedPower {k : ℕ} (r p : Simplex k) (xi alpha : ℝ) (l : Fin k) : ℝ :=
  if 2*xi < prob r l then prob p l ^ alpha else 0

def restrictedSum {k : ℕ} (r p : Simplex k) (xi alpha : ℝ) : ℝ :=
  ∑ l : Fin k, restrictedPower r p xi alpha l

def restrictedWeight {k : ℕ} (r p : Simplex k) (xi alpha : ℝ) (l : Fin k) : ℝ :=
  restrictedPower r p xi alpha l / restrictedSum r p xi alpha

theorem restrictedPower_nonneg {k : ℕ} (r p : Simplex k) (xi alpha : ℝ)
    (l : Fin k) : 0 ≤ restrictedPower r p xi alpha l := by
  unfold restrictedPower
  split_ifs
  · exact Real.rpow_nonneg (prob_nonneg p l) alpha
  · exact le_rfl

theorem restrictedSum_pos {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi C alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (hreg : P.IsRegular xi C) (i : Fin P.cellCount) (p : Simplex k)
    (hp : P.classify p = i) : 0 < restrictedSum (P.rep i) p xi alpha := by
  obtain ⟨l, hl⟩ := exists_prob_ge_inv_card (by omega : 0 < k) (P.rep i)
  have hg : 2*xi < prob (P.rep i) l := (cutoff_small hk hxi hxiK).2.1.trans_le hl
  have hactual : 0 < prob p l := hxi.trans (hreg.good_digit i p l hp hg).1
  have hterm : 0 < restrictedPower (P.rep i) p xi alpha l := by
    simpa [restrictedPower, hg] using Real.rpow_pos_of_pos hactual alpha
  exact hterm.trans_le (Finset.single_le_sum
    (fun a _ => restrictedPower_nonneg _ _ _ _ a) (Finset.mem_univ l))

theorem retainedTilt_denominator_pos {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (i : Fin P.cellCount) :
    0 < ∑ l : Fin k, if 2*xi < prob (P.rep i) l then (prob (P.rep i) l)^alpha else 0 := by
  obtain ⟨l, hl⟩ := exists_prob_ge_inv_card (by omega : 0 < k) (P.rep i)
  have hg : 2*xi < prob (P.rep i) l := (cutoff_small hk hxi hxiK).2.1.trans_le hl
  have hpos : 0 < prob (P.rep i) l := by linarith
  have hterm : 0 < restrictedPower (P.rep i) (P.rep i) xi alpha l := by
    simpa [restrictedPower, hg] using Real.rpow_pos_of_pos hpos alpha
  exact hterm.trans_le (Finset.single_le_sum
    (fun a _ => restrictedPower_nonneg _ _ _ _ a) (Finset.mem_univ l))

theorem retainedTilt_nonneg {k : ℕ} (P : BorelPartition k) (xi alpha : ℝ)
    (i : Fin P.cellCount) (l : Fin k) : 0 ≤ retainedTilt P xi alpha i l := by
  exact div_nonneg (restrictedPower_nonneg _ _ _ _ _)
    (Finset.sum_nonneg fun a _ => restrictedPower_nonneg _ _ _ _ a)

theorem retainedTilt_sum {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (i : Fin P.cellCount) : ∑ l : Fin k, retainedTilt P xi alpha i l = 1 := by
  unfold retainedTilt
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (retainedTilt_denominator_pos hk P hxi hxiK i))

theorem retainedTilt_eq_zero_of_omitted {k : ℕ} (P : BorelPartition k)
    (xi alpha : ℝ) (i : Fin P.cellCount) (l : Fin k)
    (hl : prob (P.rep i) l ≤ 2*xi) : retainedTilt P xi alpha i l = 0 := by
  simp [retainedTilt, not_lt.mpr hl]

theorem retainedTilt_pos_of_retained {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (i : Fin P.cellCount) (l : Fin k) (hl : 2*xi < prob (P.rep i) l) :
    0 < retainedTilt P xi alpha i l := by
  have hp : 0 < prob (P.rep i) l := by linarith
  exact div_pos (by simpa only [if_pos hl] using Real.rpow_pos_of_pos hp alpha)
    (retainedTilt_denominator_pos hk P hxi hxiK i)

theorem retainedTilt_le_one {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (i : Fin P.cellCount) (l : Fin k) : retainedTilt P xi alpha i l ≤ 1 := by
  rw [← retainedTilt_sum hk P hxi hxiK i]
  exact Finset.single_le_sum (fun a _ => retainedTilt_nonneg P xi alpha i a)
    (Finset.mem_univ l)

theorem powerSum_card_lower {k : ℕ} (hk : 2 ≤ k) (p : Simplex k)
    {alpha : ℝ} (ha : alpha ∈ Icc (2 : ℝ) 4) :
    1 ≤ (k : ℝ)^4 * powerSum p alpha := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨l, hl⟩ := exists_prob_ge_inv_card (by omega : 0 < k) p
  have hmul : 1 ≤ prob p l * (k : ℝ) := (div_le_iff₀ hkpos).mp hl
  have hpow : (prob p l)^4 ≤ prob p l ^ alpha := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' (prob_nonneg p l)
      (prob_le_one p l) (by linarith [ha.1] : 0 ≤ alpha) ha.2
  have hfour : 1 ≤ (prob p l * (k : ℝ))^4 := one_le_pow₀ hmul
  calc
    1 ≤ (k : ℝ)^4 * (prob p l)^4 := by nlinarith [hfour]
    _ ≤ (k : ℝ)^4 * (prob p l)^alpha :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (k : ℝ)^4 * powerSum p alpha := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun a _ => Real.rpow_nonneg (prob_nonneg p a) alpha)
        (Finset.mem_univ l)) (by positivity)

theorem fullPowerSum_pos {k : ℕ} (hk : 2 ≤ k) (p : Simplex k)
    {alpha : ℝ} (ha : alpha ∈ Icc (2 : ℝ) 4) : 0 < powerSum p alpha := by
  have h := powerSum_card_lower hk p ha
  have hkpow : 0 ≤ (k : ℝ)^4 := by positivity
  by_contra hh
  have := mul_nonpos_of_nonneg_of_nonpos hkpow (le_of_not_gt hh)
  linarith

theorem restrictedWeight_nonneg {k : ℕ} (r p : Simplex k) (xi alpha : ℝ)
    (l : Fin k) : 0 ≤ restrictedWeight r p xi alpha l :=
  div_nonneg (restrictedPower_nonneg _ _ _ _ _)
    (Finset.sum_nonneg fun a _ => restrictedPower_nonneg _ _ _ _ a)

theorem restrictedWeight_sum {k : ℕ} (r p : Simplex k) (xi alpha : ℝ)
    (hZ : 0 < restrictedSum r p xi alpha) :
    ∑ l : Fin k, restrictedWeight r p xi alpha l = 1 := by
  unfold restrictedWeight
  rw [← Finset.sum_div]
  exact div_self hZ.ne'

theorem entropy_eq_cost_log {k : ℕ} (p : Simplex k) (q : Fin k → ℝ)
    (alpha Z : ℝ) (hZ : 0 < Z) (hsum : ∑ l, q l = 1)
    (hform : ∀ l, q l ≠ 0 → 0 < prob p l ∧ q l = prob p l ^ alpha / Z) :
    shannonEntropy q = alpha * (∑ l, q l * digitCost (prob p l)) + Real.log Z := by
  have hterm (l : Fin k) :
      -(if q l = 0 then 0 else q l * Real.log (q l)) =
        alpha * (q l * digitCost (prob p l)) + q l * Real.log Z := by
    by_cases hl : q l = 0
    · simp [hl]
    · obtain ⟨hp, hq⟩ := hform l hl
      have hlog : Real.log (q l) = alpha * Real.log (prob p l) - Real.log Z := by
        rw [hq, Real.log_div (Real.rpow_pos_of_pos hp alpha).ne' hZ.ne',
          Real.log_rpow hp alpha]
      simp only [if_neg hl, hlog, digitCost, one_div, Real.log_inv]
      ring
  unfold shannonEntropy
  rw [← Finset.sum_neg_distrib]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hsum, one_mul]

theorem restrictedEntropy_identity {k : ℕ} (r p : Simplex k) (xi alpha : ℝ)
    (hZ : 0 < restrictedSum r p xi alpha)
    (hsupport : ∀ l, 2*xi < prob r l → 0 < prob p l) :
    shannonEntropy (restrictedWeight r p xi alpha) =
      alpha * (∑ l, restrictedWeight r p xi alpha l * digitCost (prob p l)) +
        Real.log (restrictedSum r p xi alpha) := by
  apply entropy_eq_cost_log p _ _ _ hZ (restrictedWeight_sum r p xi alpha hZ)
  intro l hl
  have hg : 2*xi < prob r l := by
    by_contra hg
    exact hl (by simp [restrictedWeight, restrictedPower, hg])
  exact ⟨hsupport l hg, by simp [restrictedWeight, restrictedPower, hg]⟩

theorem tiltedEntropy_identity {k : ℕ} (hk : 2 ≤ k) (p : Simplex k)
    {alpha : ℝ} (ha : alpha ∈ Icc (2 : ℝ) 4) :
    tiltedEntropy p alpha = alpha * tiltedCost p alpha + Real.log (powerSum p alpha) := by
  have hZ := fullPowerSum_pos hk p ha
  have hsum : ∑ l, tiltedWeight p alpha l = 1 := by
    unfold tiltedWeight
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hform (l : Fin k) (hl : tiltedWeight p alpha l ≠ 0) :
      0 < prob p l ∧ tiltedWeight p alpha l = prob p l ^ alpha / powerSum p alpha := by
    refine ⟨?_, rfl⟩
    apply lt_of_le_of_ne (prob_nonneg p l)
    intro hz
    exact hl (by simp [tiltedWeight, ← hz, Real.zero_rpow (by linarith [ha.1] : alpha ≠ 0)])
  have h := entropy_eq_cost_log p (tiltedWeight p alpha) alpha (powerSum p alpha) hZ hsum hform
  have hc : (∑ l, tiltedWeight p alpha l * digitCost (prob p l)) = tiltedCost p alpha := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : prob p l = 0
    · simp [hl, digitCost]
    · simp [hl]
  simpa only [tiltedEntropy, hc] using h

theorem digitCost_nonneg {k : ℕ} (p : Simplex k) (l : Fin k) :
    0 ≤ digitCost (prob p l) := by
  by_cases hl : prob p l = 0
  · simp [digitCost, hl]
  · have hp : 0 < prob p l := lt_of_le_of_ne (prob_nonneg p l) (Ne.symm hl)
    exact Real.log_nonneg ((one_le_div hp).mpr (prob_le_one p l))

theorem restrictedCost_bounds {k : ℕ} (r p : Simplex k) {xi alpha : ℝ}
    (hxi : 0 < xi) (hZ : 0 < restrictedSum r p xi alpha)
    (hsupport : ∀ l, 2*xi < prob r l → xi ≤ prob p l) :
    0 ≤ (∑ l, restrictedWeight r p xi alpha l * digitCost (prob p l)) ∧
    (∑ l, restrictedWeight r p xi alpha l * digitCost (prob p l)) ≤ Real.log (1/xi) := by
  constructor
  · exact Finset.sum_nonneg fun l _ => mul_nonneg (restrictedWeight_nonneg _ _ _ _ _)
      (digitCost_nonneg p l)
  · calc
      (∑ l, restrictedWeight r p xi alpha l * digitCost (prob p l)) ≤
          ∑ l, restrictedWeight r p xi alpha l * Real.log (1/xi) := by
        apply Finset.sum_le_sum
        intro l _
        by_cases hg : 2*xi < prob r l
        · apply mul_le_mul_of_nonneg_left _ (restrictedWeight_nonneg _ _ _ _ _)
          exact Real.log_le_log (one_div_pos.mpr (hxi.trans_le (hsupport l hg)))
            (one_div_le_one_div_of_le hxi (hsupport l hg))
        · simp [restrictedWeight, restrictedPower, hg]
      _ = Real.log (1/xi) := by
        rw [← Finset.sum_mul, restrictedWeight_sum r p xi alpha hZ, one_mul]

private theorem powers_close {p r d alpha : ℝ} (hp : 0 < p) (hr : 0 < r)
    (hd : 0 ≤ d) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (hcost : |digitCost p - digitCost r| ≤ d) :
    p^alpha ≤ Real.exp (4*d)*r^alpha ∧ r^alpha ≤ Real.exp (4*d)*p^alpha := by
  have habs : |Real.log r - Real.log p| ≤ d := by
    simpa only [digitCost, one_div, Real.log_inv, neg_sub_neg] using hcost
  have h1 := (abs_le.mp habs).1
  have h2 := (abs_le.mp habs).2
  have ha0 : 0 ≤ alpha := by linarith [ha.1]
  have hmul1 := mul_le_mul_of_nonneg_right h1 ha0
  have hmul2 := mul_le_mul_of_nonneg_right h2 ha0
  have hbound := mul_le_mul_of_nonneg_right ha.2 hd
  constructor
  · rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hr, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hr, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)

private theorem normalized_le {k : ℕ} (a b : Fin k → ℝ) (E : ℝ)
    (_ha : ∀ l, 0 ≤ a l) (hb : ∀ l, 0 ≤ b l) (hE : 0 ≤ E)
    (hA : 0 < ∑ l, a l) (hB : 0 < ∑ l, b l)
    (hab : ∀ l, a l ≤ E*b l) (hba : ∀ l, b l ≤ E*a l) (l : Fin k) :
    a l / (∑ t, a t) ≤ E^2 * (b l / (∑ t, b t)) := by
  have hsum : (∑ t, b t) ≤ E * ∑ t, a t := by
    simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun t _ => hba t)
  rw [← mul_div_assoc, div_le_div_iff₀ hA hB]
  have hprod := mul_le_mul (hab l) hsum hB.le (mul_nonneg hE (hb l))
  nlinarith [hprod]

private theorem abs_sub_le_of_ratios {a b E : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hE : 1 ≤ E) (hab : a ≤ E*b) (hba : b ≤ E*a) :
    |a-b| ≤ (E-1)*b := by
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hinv : 2-E ≤ 1/E := (le_div_iff₀ hEpos).mpr (by nlinarith [sq_nonneg (E-1)])
  have hquot : b/E ≤ a := (div_le_iff₀ hEpos).mpr (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_right hinv hb
  have hid : 1/E*b = b/E := by ring
  rw [hid] at hmul
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem restrictedWeight_cell_error {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi C alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (hC : 0 ≤ C) (hreg : P.IsRegular xi C) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (i : Fin P.cellCount) (p : Simplex k) (hp : P.classify p = i) (l : Fin k) :
    |restrictedWeight (P.rep i) (P.rep i) xi alpha l -
      restrictedWeight (P.rep i) p xi alpha l| ≤
      (Real.exp (8*C*xi)-1) * restrictedWeight (P.rep i) p xi alpha l := by
  let a := restrictedPower (P.rep i) (P.rep i) xi alpha
  let b := restrictedPower (P.rep i) p xi alpha
  have hcompare (t : Fin k) :
      a t ≤ Real.exp (4*(C*xi))*b t ∧ b t ≤ Real.exp (4*(C*xi))*a t := by
    by_cases hg : 2*xi < prob (P.rep i) t
    · have hr : 0 < prob (P.rep i) t := by linarith
      have hactual := hreg.good_digit i p t hp hg
      have hpair := powers_close (hxi.trans hactual.1) hr (mul_nonneg hC hxi.le) ha hactual.2
      simpa only [a, b, restrictedPower, if_pos hg] using hpair.symm
    · simp [a, b, restrictedPower, hg]
  have hA : 0 < ∑ t, a t := retainedTilt_denominator_pos hk P hxi hxiK i
  have hB : 0 < ∑ t, b t := restrictedSum_pos hk P hxi hxiK hreg i p hp
  have heq : (Real.exp (4*(C*xi)))^2 = Real.exp (8*C*xi) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hab := normalized_le a b (Real.exp (4*(C*xi)))
    (restrictedPower_nonneg _ _ _ _) (restrictedPower_nonneg _ _ _ _)
    (Real.exp_pos _).le hA hB (fun t => (hcompare t).1) (fun t => (hcompare t).2) l
  have hba := normalized_le b a (Real.exp (4*(C*xi)))
    (restrictedPower_nonneg _ _ _ _) (restrictedPower_nonneg _ _ _ _)
    (Real.exp_pos _).le hB hA (fun t => (hcompare t).2) (fun t => (hcompare t).1) l
  rw [heq] at hab hba
  exact abs_sub_le_of_ratios (restrictedWeight_nonneg _ _ _ _ _)
    (restrictedWeight_nonneg _ _ _ _ _)
    (Real.one_le_exp_iff.mpr (by positivity)) hab hba

theorem exp_cell_error {xi C : ℝ} (hxi : 0 ≤ xi) (hsmall : xi ≤ 1/8)
    (hC : 0 ≤ C) : Real.exp (8*C*xi)-1 ≤ 8*C*Real.exp C*xi := by
  let x : ℝ := 8*C*xi
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxc : x ≤ C := by dsimp [x]; nlinarith
  have h := Real.add_one_le_exp (-x)
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos x).le
  have hcancel : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  rw [hcancel] at hm
  have hfirst : Real.exp x - 1 ≤ x * Real.exp x := by nlinarith
  have hsecond := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxc) hx
  dsimp [x] at hfirst hsecond
  nlinarith

theorem restrictedCost_cell_error {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi C alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (hC : 0 ≤ C) (hreg : P.IsRegular xi C) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (i : Fin P.cellCount) (p : Simplex k) (hp : P.classify p = i) :
    |(∑ l, restrictedWeight (P.rep i) (P.rep i) xi alpha l * digitCost (prob p l)) -
      (∑ l, restrictedWeight (P.rep i) p xi alpha l * digitCost (prob p l))| ≤
      8*C*Real.exp C*xi*Real.log (1/xi) := by
  have hZ := restrictedSum_pos hk P (alpha := alpha) hxi hxiK hreg i p hp
  have hcost := restrictedCost_bounds (P.rep i) p hxi hZ
    (fun l hg => (hreg.good_digit i p l hp hg).1.le)
  have hcoef : 0 ≤ Real.exp (8*C*xi)-1 := by
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  calc
    _ = |∑ l, (restrictedWeight (P.rep i) (P.rep i) xi alpha l -
        restrictedWeight (P.rep i) p xi alpha l) * digitCost (prob p l)| := by
      congr 1
      simp_rw [sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ l, |(restrictedWeight (P.rep i) (P.rep i) xi alpha l -
        restrictedWeight (P.rep i) p xi alpha l) * digitCost (prob p l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, ((Real.exp (8*C*xi)-1) * restrictedWeight (P.rep i) p xi alpha l) *
        digitCost (prob p l) := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_of_nonneg (digitCost_nonneg p l)]
      exact mul_le_mul_of_nonneg_right
        (restrictedWeight_cell_error hk P hxi hxiK hC hreg ha i p hp l)
        (digitCost_nonneg p l)
    _ = (Real.exp (8*C*xi)-1) *
        (∑ l, restrictedWeight (P.rep i) p xi alpha l * digitCost (prob p l)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ (Real.exp (8*C*xi)-1) * Real.log (1/xi) :=
      mul_le_mul_of_nonneg_left hcost.2 hcoef
    _ ≤ 8*C*Real.exp C*xi*Real.log (1/xi) :=
      mul_le_mul_of_nonneg_right
        (exp_cell_error hxi.le (cutoff_small hk hxi hxiK).1.le hC)
        (le_trans (by norm_num) (cutoff_log_ge_one hxi (cutoff_small hk hxi hxiK).1))

def omittedPower {k : ℕ} (r p : Simplex k) (xi alpha : ℝ) (l : Fin k) : ℝ :=
  if prob r l ≤ 2*xi then prob p l ^ alpha else 0

def omittedSum {k : ℕ} (r p : Simplex k) (xi alpha : ℝ) : ℝ :=
  ∑ l, omittedPower r p xi alpha l

def omittedCostSum {k : ℕ} (r p : Simplex k) (xi alpha : ℝ) : ℝ :=
  ∑ l, omittedPower r p xi alpha l * digitCost (prob p l)

theorem omittedPower_nonneg {k : ℕ} (r p : Simplex k) (xi alpha : ℝ)
    (l : Fin k) : 0 ≤ omittedPower r p xi alpha l := by
  unfold omittedPower
  split_ifs
  · exact Real.rpow_nonneg (prob_nonneg p l) alpha
  · exact le_rfl

theorem powerSum_split {k : ℕ} (r p : Simplex k) (xi alpha : ℝ) :
    powerSum p alpha = restrictedSum r p xi alpha + omittedSum r p xi alpha := by
  rw [restrictedSum, omittedSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hg : 2*xi < prob r l
  · simp [restrictedPower, omittedPower, hg, not_le.mpr hg]
  · simp [restrictedPower, omittedPower, hg, le_of_not_gt hg]

theorem omittedSum_le {k : ℕ} (r p : Simplex k) {xi alpha : ℝ} (_hxi : 0 ≤ xi)
    (ha : alpha ∈ Icc (2 : ℝ) 4)
    (hbad : ∀ l, prob r l ≤ 2*xi → prob p l ≤ 3*xi) :
    omittedSum r p xi alpha ≤ 9*(k : ℝ)*xi^2 := by
  have hterm (l : Fin k) : omittedPower r p xi alpha l ≤ 9*xi^2 := by
    unfold omittedPower
    split_ifs with hg
    · have hp2 : prob p l ^ alpha ≤ (prob p l)^2 := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' (prob_nonneg p l)
          (prob_le_one p l) (by norm_num : (0 : ℝ) ≤ 2) ha.1
      have hs := pow_le_pow_left₀ (prob_nonneg p l) (hbad l hg) 2
      nlinarith
    · positivity
  have hs := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) => hterm l)
  simpa [omittedSum, mul_assoc, mul_left_comm, mul_comm] using hs

theorem power_digitCost_le_prob {k : ℕ} (p : Simplex k) {alpha : ℝ}
    (ha : alpha ∈ Icc (2 : ℝ) 4) (l : Fin k) :
    prob p l ^ alpha * digitCost (prob p l) ≤ prob p l := by
  by_cases hl : prob p l = 0
  · simp [hl, digitCost]
  · have hp : 0 < prob p l := lt_of_le_of_ne (prob_nonneg p l) (Ne.symm hl)
    have hp2 : prob p l ^ alpha ≤ (prob p l)^2 := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' (prob_nonneg p l)
        (prob_le_one p l) (by norm_num : (0 : ℝ) ≤ 2) ha.1
    have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr hp)
    have hm := mul_le_mul_of_nonneg_left hlog (sq_nonneg (prob p l))
    have hid : (prob p l)^2 * (1 / prob p l - 1) = prob p l - (prob p l)^2 := by
      field_simp
    rw [hid] at hm
    calc
      _ ≤ (prob p l)^2 * digitCost (prob p l) :=
        mul_le_mul_of_nonneg_right hp2 (digitCost_nonneg p l)
      _ ≤ prob p l := by unfold digitCost; nlinarith [sq_nonneg (prob p l)]

theorem omittedCostSum_le {k : ℕ} (r p : Simplex k) {xi alpha : ℝ} (hxi : 0 ≤ xi)
    (ha : alpha ∈ Icc (2 : ℝ) 4)
    (hbad : ∀ l, prob r l ≤ 2*xi → prob p l ≤ 3*xi) :
    omittedCostSum r p xi alpha ≤ 3*(k : ℝ)*xi := by
  have hterm (l : Fin k) : omittedPower r p xi alpha l * digitCost (prob p l) ≤ 3*xi := by
    unfold omittedPower
    split_ifs with hg
    · exact (power_digitCost_le_prob p ha l).trans (hbad l hg)
    · simp only [zero_mul]; positivity
  have hs := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) => hterm l)
  simpa [omittedCostSum, mul_assoc, mul_left_comm, mul_comm] using hs

theorem tiltedCost_eq_raw {k : ℕ} (p : Simplex k) (alpha : ℝ) :
    tiltedCost p alpha = (∑ l, prob p l ^ alpha * digitCost (prob p l)) / powerSum p alpha := by
  rw [Finset.sum_div]
  unfold tiltedCost tiltedWeight
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : prob p l = 0
  · simp [hl, digitCost]
  · simp only [if_neg hl]
    ring

theorem restrictedCost_eq_raw {k : ℕ} (r p : Simplex k) (xi alpha : ℝ) :
    (∑ l, restrictedWeight r p xi alpha l * digitCost (prob p l)) =
      (∑ l, restrictedPower r p xi alpha l * digitCost (prob p l)) /
        restrictedSum r p xi alpha := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  unfold restrictedWeight
  ring

theorem tiltedCost_split {k : ℕ} (r p : Simplex k) (xi alpha : ℝ)
    (hZ : 0 < powerSum p alpha) (hG : 0 < restrictedSum r p xi alpha) :
    tiltedCost p alpha = (restrictedSum r p xi alpha / powerSum p alpha) *
      (∑ l, restrictedWeight r p xi alpha l * digitCost (prob p l)) +
        omittedCostSum r p xi alpha / powerSum p alpha := by
  have hnum : (∑ l, prob p l ^ alpha * digitCost (prob p l)) =
      (∑ l, restrictedPower r p xi alpha l * digitCost (prob p l)) +
        omittedCostSum r p xi alpha := by
    rw [omittedCostSum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hg : 2*xi < prob r l
    · simp [restrictedPower, omittedPower, hg, not_le.mpr hg]
    · simp [restrictedPower, omittedPower, hg, le_of_not_gt hg]
  rw [tiltedCost_eq_raw, restrictedCost_eq_raw, hnum]
  field_simp

private theorem div_le_mul_of_one_le_mul {a Z M : ℝ} (ha : 0 ≤ a) (hZ : 0 < Z)
    (hMZ : 1 ≤ M*Z) : a/Z ≤ M*a := by
  apply (div_le_iff₀ hZ).mpr
  have h := mul_le_mul_of_nonneg_right hMZ ha
  nlinarith

theorem omittedTiltedSum_le {k : ℕ} (hk : 2 ≤ k) (r p : Simplex k)
    {xi alpha : ℝ} (hxi : 0 ≤ xi) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (hbad : ∀ l, prob r l ≤ 2*xi → prob p l ≤ 3*xi) :
    omittedSum r p xi alpha / powerSum p alpha ≤ 9*(k : ℝ)^5*xi^2 := by
  calc
    _ ≤ (k : ℝ)^4 * omittedSum r p xi alpha :=
      div_le_mul_of_one_le_mul
        (Finset.sum_nonneg fun l _ => omittedPower_nonneg _ _ _ _ _)
        (fullPowerSum_pos hk p ha) (powerSum_card_lower hk p ha)
    _ ≤ (k : ℝ)^4 * (9*(k : ℝ)*xi^2) :=
      mul_le_mul_of_nonneg_left (omittedSum_le r p hxi ha hbad) (by positivity)
    _ = 9*(k : ℝ)^5*xi^2 := by ring

theorem omittedTiltedCost_le {k : ℕ} (hk : 2 ≤ k) (r p : Simplex k)
    {xi alpha : ℝ} (hxi : 0 ≤ xi) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (hbad : ∀ l, prob r l ≤ 2*xi → prob p l ≤ 3*xi) :
    omittedCostSum r p xi alpha / powerSum p alpha ≤ 3*(k : ℝ)^5*xi := by
  calc
    _ ≤ (k : ℝ)^4 * omittedCostSum r p xi alpha :=
      div_le_mul_of_one_le_mul
        (Finset.sum_nonneg fun l _ => mul_nonneg (omittedPower_nonneg _ _ _ _ _)
          (digitCost_nonneg p l))
        (fullPowerSum_pos hk p ha) (powerSum_card_lower hk p ha)
    _ ≤ (k : ℝ)^4 * (3*(k : ℝ)*xi) :=
      mul_le_mul_of_nonneg_left (omittedCostSum_le r p hxi ha hbad) (by positivity)
    _ = 3*(k : ℝ)^5*xi := by ring

theorem restrictedCost_truncation_error {k : ℕ} (hk : 2 ≤ k) (r p : Simplex k)
    {xi alpha : ℝ} (hxi : 0 < xi) (hsmall : xi < 1/8)
    (ha : alpha ∈ Icc (2 : ℝ) 4) (hG : 0 < restrictedSum r p xi alpha)
    (hsupport : ∀ l, 2*xi < prob r l → xi ≤ prob p l)
    (hbad : ∀ l, prob r l ≤ 2*xi → prob p l ≤ 3*xi) :
    |(∑ l, restrictedWeight r p xi alpha l * digitCost (prob p l)) - tiltedCost p alpha| ≤
      18*(k : ℝ)^5*xi*Real.log (1/xi) := by
  let c := ∑ l, restrictedWeight r p xi alpha l * digitCost (prob p l)
  let d := omittedSum r p xi alpha / powerSum p alpha
  let o := omittedCostSum r p xi alpha / powerSum p alpha
  let B := Real.log (1/xi)
  have hZ := fullPowerSum_pos hk p ha
  have hB : 1 ≤ B := cutoff_log_ge_one hxi hsmall
  have hcost : 0 ≤ c ∧ c ≤ B := restrictedCost_bounds r p hxi hG hsupport
  have hd : 0 ≤ d := div_nonneg
    (Finset.sum_nonneg fun l _ => omittedPower_nonneg _ _ _ _ _) hZ.le
  have ho : 0 ≤ o := div_nonneg
    (Finset.sum_nonneg fun l _ => mul_nonneg (omittedPower_nonneg _ _ _ _ _)
      (digitCost_nonneg p l)) hZ.le
  have hid : c - tiltedCost p alpha = d*c-o := by
    rw [tiltedCost_split r p xi alpha hZ hG]
    change c - (restrictedSum r p xi alpha / powerSum p alpha * c + o) = d*c-o
    dsimp [d]
    have hz := powerSum_split r p xi alpha
    field_simp
    nlinarith
  have hdB := mul_le_mul_of_nonneg_left hcost.2 hd
  have habs : |c-tiltedCost p alpha| ≤ d*B+o := by
    rw [hid]
    exact abs_le.mpr ⟨by nlinarith [mul_nonneg hd hcost.1], by nlinarith⟩
  have hd_bound : d ≤ 9*(k : ℝ)^5*xi^2 := omittedTiltedSum_le hk r p hxi.le ha hbad
  have ho_bound : o ≤ 3*(k : ℝ)^5*xi := omittedTiltedCost_le hk r p hxi.le ha hbad
  have hxi1 : xi ≤ 1 := by linarith
  have hpow : xi^2 ≤ xi := by nlinarith
  have hB0 : 0 ≤ B := by linarith
  have hm1 := mul_le_mul_of_nonneg_right hd_bound hB0
  have hm2 := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 9*(k : ℝ)^5*B by positivity)
  have hm3 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*(k : ℝ)^5*xi by positivity)
  change |c-tiltedCost p alpha| ≤ 18*(k : ℝ)^5*xi*B
  nlinarith [show 0 ≤ (k : ℝ)^5*xi*B by positivity]

def truncationCostConstant (k : ℕ) (C : ℝ) : ℝ :=
  C + 8*C*Real.exp C + 18*(k : ℝ)^5

def truncationEntropyConstant (k : ℕ) (C : ℝ) : ℝ :=
  4*truncationCostConstant k C + 4*C + 9*(k : ℝ)^5

theorem representativeCost_error {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi C alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (hreg : P.IsRegular xi C) (i : Fin P.cellCount) (p : Simplex k)
    (hp : P.classify p = i) :
    |(∑ l, retainedTilt P xi alpha i l * digitCost (prob (P.rep i) l)) -
      (∑ l, retainedTilt P xi alpha i l * digitCost (prob p l))| ≤ C*xi := by
  calc
    _ = |∑ l, retainedTilt P xi alpha i l *
        (digitCost (prob (P.rep i) l) - digitCost (prob p l))| := by
      congr 1
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ l, |retainedTilt P xi alpha i l *
        (digitCost (prob (P.rep i) l) - digitCost (prob p l))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, retainedTilt P xi alpha i l * (C*xi) := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_of_nonneg (retainedTilt_nonneg P xi alpha i l)]
      by_cases hg : 2*xi < prob (P.rep i) l
      · apply mul_le_mul_of_nonneg_left _ (retainedTilt_nonneg P xi alpha i l)
        simpa only [abs_sub_comm] using (hreg.good_digit i p l hp hg).2
      · simp [retainedTilt_eq_zero_of_omitted P xi alpha i l (le_of_not_gt hg)]
    _ = C*xi := by rw [← Finset.sum_mul, retainedTilt_sum hk P hxi hxiK i, one_mul]

theorem retainedTilt_cost_transfer {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi C alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (hC : 0 ≤ C) (hreg : P.IsRegular xi C) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (i : Fin P.cellCount) (p : Simplex k) (hp : P.classify p = i) :
    |(∑ l, retainedTilt P xi alpha i l * digitCost (prob (P.rep i) l)) - tiltedCost p alpha| ≤
      truncationCostConstant k C * xi * Real.log (1/xi) := by
  have h1 := representativeCost_error hk P (alpha := alpha) hxi hxiK hreg i p hp
  have h2 := restrictedCost_cell_error hk P hxi hxiK hC hreg ha i p hp
  have h3 := restrictedCost_truncation_error hk (P.rep i) p hxi (cutoff_small hk hxi hxiK).1
    ha (restrictedSum_pos hk P hxi hxiK hreg i p hp)
    (fun l hg => (hreg.good_digit i p l hp hg).1.le)
    (fun l hg => hreg.exceptional_digit i p l hp hg)
  change |(∑ l, retainedTilt P xi alpha i l * digitCost (prob p l)) -
    (∑ l, restrictedWeight (P.rep i) p xi alpha l * digitCost (prob p l))| ≤ _ at h2
  have ht1 := abs_sub_le
    (∑ l, retainedTilt P xi alpha i l * digitCost (prob (P.rep i) l))
    (∑ l, retainedTilt P xi alpha i l * digitCost (prob p l))
    (tiltedCost p alpha)
  have ht2 := abs_sub_le
    (∑ l, retainedTilt P xi alpha i l * digitCost (prob p l))
    (∑ l, restrictedWeight (P.rep i) p xi alpha l * digitCost (prob p l))
    (tiltedCost p alpha)
  have hB := cutoff_log_ge_one hxi (cutoff_small hk hxi hxiK).1
  have hm := mul_le_mul_of_nonneg_left hB (mul_nonneg hC hxi.le)
  unfold truncationCostConstant
  nlinarith

theorem restrictedSum_rep_card_lower {k : ℕ} (hk : 2 ≤ k) (r : Simplex k)
    {xi alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (ha : alpha ∈ Icc (2 : ℝ) 4) :
    1 ≤ (k : ℝ)^4 * restrictedSum r r xi alpha := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨l, hl⟩ := exists_prob_ge_inv_card (by omega : 0 < k) r
  have hg : 2*xi < prob r l := (cutoff_small hk hxi hxiK).2.1.trans_le hl
  have hmul : 1 ≤ prob r l * (k : ℝ) := (div_le_iff₀ hkpos).mp hl
  have hpow : (prob r l)^4 ≤ prob r l ^ alpha := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' (prob_nonneg r l)
      (prob_le_one r l) (by linarith [ha.1] : 0 ≤ alpha) ha.2
  have hfour : 1 ≤ (prob r l * (k : ℝ))^4 := one_le_pow₀ hmul
  have hterm : prob r l ^ alpha ≤ restrictedSum r r xi alpha := by
    have ht := Finset.single_le_sum (fun a _ => restrictedPower_nonneg r r xi alpha a)
      (Finset.mem_univ l)
    simpa only [restrictedSum, restrictedPower, if_pos hg] using ht
  calc
    1 ≤ (k : ℝ)^4 * (prob r l)^4 := by nlinarith [hfour]
    _ ≤ (k : ℝ)^4 * (prob r l)^alpha :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (k : ℝ)^4 * restrictedSum r r xi alpha :=
      mul_le_mul_of_nonneg_left hterm (by positivity)

theorem restrictedLog_rep_error {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (ha : alpha ∈ Icc (2 : ℝ) 4) (i : Fin P.cellCount) :
    |Real.log (restrictedSum (P.rep i) (P.rep i) xi alpha) -
      Real.log (powerSum (P.rep i) alpha)| ≤ 9*(k : ℝ)^5*xi^2 := by
  let r := P.rep i
  have hZ := fullPowerSum_pos hk r ha
  have hG : 0 < restrictedSum r r xi alpha := retainedTilt_denominator_pos hk P hxi hxiK i
  have hO : 0 ≤ omittedSum r r xi alpha :=
    Finset.sum_nonneg fun l _ => omittedPower_nonneg _ _ _ _ _
  have hsplit := powerSum_split r r xi alpha
  have hle : restrictedSum r r xi alpha ≤ powerSum r alpha := by linarith
  have hlogle := Real.log_le_log hG hle
  have hlog := Real.log_le_sub_one_of_pos (div_pos hZ hG)
  rw [Real.log_div hZ.ne' hG.ne'] at hlog
  have hratio : powerSum r alpha / restrictedSum r r xi alpha - 1 =
      omittedSum r r xi alpha / restrictedSum r r xi alpha := by
    field_simp
    linarith
  rw [hratio] at hlog
  have hdiv := div_le_mul_of_one_le_mul hO hG
    (restrictedSum_rep_card_lower hk r hxi hxiK ha)
  have hraw := omittedSum_le r r hxi.le ha (fun l hl => by linarith)
  have hmul := mul_le_mul_of_nonneg_left hraw (show 0 ≤ (k : ℝ)^4 by positivity)
  change |Real.log (restrictedSum r r xi alpha) - Real.log (powerSum r alpha)| ≤ _
  rw [abs_of_nonpos (sub_nonpos.mpr hlogle)]
  nlinarith

theorem retainedTilt_entropy_transfer {k : ℕ} (hk : 2 ≤ k) (P : BorelPartition k)
    {xi C alpha : ℝ} (hxi : 0 < xi) (hxiK : xi < 1/(4*(k : ℝ)))
    (hC : 0 ≤ C) (hreg : P.IsRegular xi C) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (i : Fin P.cellCount) (p : Simplex k) (hp : P.classify p = i) :
    |shannonEntropy (retainedTilt P xi alpha i) - tiltedEntropy p alpha| ≤
      truncationEntropyConstant k C * xi * Real.log (1/xi) := by
  have hc := retainedTilt_cost_transfer hk P hxi hxiK hC hreg ha i p hp
  have hlog1 := restrictedLog_rep_error hk P hxi hxiK ha i
  have hlog2 : |Real.log (powerSum (P.rep i) alpha) - Real.log (powerSum p alpha)| ≤ C*xi := by
    have h := hreg.psi_oscillation i (P.rep i) p (P.classify_rep i) hp alpha ha
    simpa only [psi, neg_sub_neg, abs_sub_comm] using h
  have hlogtri := abs_sub_le
    (Real.log (restrictedSum (P.rep i) (P.rep i) xi alpha))
    (Real.log (powerSum (P.rep i) alpha)) (Real.log (powerSum p alpha))
  have hG : 0 < restrictedSum (P.rep i) (P.rep i) xi alpha :=
    retainedTilt_denominator_pos hk P hxi hxiK i
  have hrep := restrictedEntropy_identity (P.rep i) (P.rep i) xi alpha hG
    (fun l hl => by linarith)
  change shannonEntropy (retainedTilt P xi alpha i) =
    alpha * (∑ l, retainedTilt P xi alpha i l * digitCost (prob (P.rep i) l)) +
      Real.log (restrictedSum (P.rep i) (P.rep i) xi alpha) at hrep
  rw [hrep, tiltedEntropy_identity hk p ha]
  have ha0 : 0 ≤ alpha := by linarith [ha.1]
  have htri := abs_add_le
    (alpha * ((∑ l, retainedTilt P xi alpha i l * digitCost (prob (P.rep i) l)) - tiltedCost p alpha))
    (Real.log (restrictedSum (P.rep i) (P.rep i) xi alpha) - Real.log (powerSum p alpha))
  rw [abs_mul, abs_of_nonneg ha0] at htri
  have hmul := mul_le_mul_of_nonneg_left hc ha0
  have hconst : 0 ≤ truncationCostConstant k C := by unfold truncationCostConstant; positivity
  have hB := cutoff_log_ge_one hxi (cutoff_small hk hxi hxiK).1
  have hB0 : 0 ≤ Real.log (1/xi) := by linarith
  have halpha := mul_le_mul_of_nonneg_right ha.2
    (show 0 ≤ truncationCostConstant k C * xi * Real.log (1/xi) by positivity)
  have hxi1 : xi ≤ 1 := by have := (cutoff_small hk hxi hxiK).1; linarith
  have hsq : xi^2 ≤ xi := by nlinarith
  have hlarge : xi ≤ xi * Real.log (1/xi) := by nlinarith
  have hpol := mul_le_mul_of_nonneg_left (hsq.trans hlarge)
    (show 0 ≤ 9*(k : ℝ)^5 by positivity)
  have hcx := mul_le_mul_of_nonneg_left hlarge hC
  have hnonneg : 0 ≤ C*xi*Real.log (1/xi) := by positivity
  have heq : alpha * (∑ l, retainedTilt P xi alpha i l * digitCost (prob (P.rep i) l)) +
      Real.log (restrictedSum (P.rep i) (P.rep i) xi alpha) -
      (alpha * tiltedCost p alpha + Real.log (powerSum p alpha)) =
      alpha * ((∑ l, retainedTilt P xi alpha i l * digitCost (prob (P.rep i) l)) - tiltedCost p alpha) +
      (Real.log (restrictedSum (P.rep i) (P.rep i) xi alpha) - Real.log (powerSum p alpha)) := by ring
  rw [heq]
  unfold truncationEntropyConstant
  nlinarith

theorem power_digitCost_small {k : ℕ} (p : Simplex k) {xi alpha : ℝ}
    (hxi : 0 < xi) (hsmall : xi < 1/8) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (l : Fin k) (hl : prob p l ≤ 3*xi) :
    prob p l ^ alpha * digitCost (prob p l) ≤ 12*xi^2*Real.log (1/xi) := by
  have hB := cutoff_log_ge_one hxi hsmall
  have hB0 : 0 ≤ Real.log (1/xi) := by linarith
  by_cases hz : prob p l = 0
  · simp only [hz, digitCost, div_zero, Real.log_zero, mul_zero]
    positivity
  · have hp : 0 < prob p l := lt_of_le_of_ne (prob_nonneg p l) (Ne.symm hz)
    have hpow : prob p l ^ alpha ≤ (prob p l)^2 := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' (prob_nonneg p l)
        (prob_le_one p l) (by norm_num : (0 : ℝ) ≤ 2) ha.1
    have hlog : digitCost (prob p l) = Real.log (1/xi) + Real.log (xi / prob p l) := by
      rw [Real.log_div hxi.ne' hp.ne']
      simp only [digitCost, one_div, Real.log_inv]
      ring
    have hlogbound := Real.log_le_sub_one_of_pos (div_pos hxi hp)
    have hm := mul_le_mul_of_nonneg_left hlogbound (sq_nonneg (prob p l))
    have hid : (prob p l)^2 * (xi / prob p l - 1) = xi * prob p l - (prob p l)^2 := by
      field_simp
    rw [hid] at hm
    have hp2 : (prob p l)^2 ≤ 9*xi^2 := by nlinarith [prob_nonneg p l]
    have hfirst := mul_le_mul_of_nonneg_right hp2 hB0
    have hsecond := mul_le_mul_of_nonneg_left hl hxi.le
    have hthird := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*xi^2 by positivity)
    calc
      _ ≤ (prob p l)^2 * digitCost (prob p l) :=
        mul_le_mul_of_nonneg_right hpow (digitCost_nonneg p l)
      _ ≤ 12*xi^2*Real.log (1/xi) := by rw [hlog]; nlinarith [sq_nonneg (prob p l)]

theorem omittedCostSum_small {k : ℕ} (r p : Simplex k) {xi alpha : ℝ}
    (hxi : 0 < xi) (hsmall : xi < 1/8) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (hbad : ∀ l, prob r l ≤ 2*xi → prob p l ≤ 3*xi) :
    omittedCostSum r p xi alpha ≤ 12*(k : ℝ)*xi^2*Real.log (1/xi) := by
  have hB0 : 0 ≤ Real.log (1/xi) := (by norm_num : (0 : ℝ) ≤ 1).trans
    (cutoff_log_ge_one hxi hsmall)
  have hterm (l : Fin k) : omittedPower r p xi alpha l * digitCost (prob p l) ≤
      12*xi^2*Real.log (1/xi) := by
    unfold omittedPower
    split_ifs with hg
    · exact power_digitCost_small p hxi hsmall ha l (hbad l hg)
    · simp only [zero_mul]; positivity
  have hs := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) => hterm l)
  simpa [omittedCostSum, mul_assoc, mul_left_comm, mul_comm] using hs

theorem omittedTiltedCost_small {k : ℕ} (hk : 2 ≤ k) (r p : Simplex k)
    {xi alpha : ℝ} (hxi : 0 < xi) (hsmall : xi < 1/8) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (hbad : ∀ l, prob r l ≤ 2*xi → prob p l ≤ 3*xi) :
    omittedCostSum r p xi alpha / powerSum p alpha ≤
      12*(k : ℝ)^5*xi^2*Real.log (1/xi) := by
  calc
    _ ≤ (k : ℝ)^4 * omittedCostSum r p xi alpha :=
      div_le_mul_of_one_le_mul
        (Finset.sum_nonneg fun l _ => mul_nonneg (omittedPower_nonneg _ _ _ _ _)
          (digitCost_nonneg p l))
        (fullPowerSum_pos hk p ha) (powerSum_card_lower hk p ha)
    _ ≤ (k : ℝ)^4 * (12*(k : ℝ)*xi^2*Real.log (1/xi)) :=
      mul_le_mul_of_nonneg_left (omittedCostSum_small r p hxi hsmall ha hbad) (by positivity)
    _ = 12*(k : ℝ)^5*xi^2*Real.log (1/xi) := by ring

def omittedEntropySum {k : ℕ} (r p : Simplex k) (xi alpha : ℝ) : ℝ :=
  ∑ l : Fin k, if prob r l ≤ 2*xi then
    -(if tiltedWeight p alpha l = 0 then 0 else
      tiltedWeight p alpha l * Real.log (tiltedWeight p alpha l)) else 0

theorem fullPowerSum_le_one {k : ℕ} (p : Simplex k)
    {alpha : ℝ} (ha : alpha ∈ Icc (2 : ℝ) 4) : powerSum p alpha ≤ 1 := by
  calc
    _ ≤ ∑ l, prob p l := Finset.sum_le_sum fun l _ =>
      Real.rpow_le_self_of_le_one (prob_nonneg p l) (prob_le_one p l) (by linarith [ha.1])
    _ = 1 := sum_prob p

theorem tiltedEntropy_term_bounds {k : ℕ} (hk : 2 ≤ k) (p : Simplex k)
    {alpha : ℝ} (ha : alpha ∈ Icc (2 : ℝ) 4) (l : Fin k) :
    0 ≤ -(if tiltedWeight p alpha l = 0 then 0 else
      tiltedWeight p alpha l * Real.log (tiltedWeight p alpha l)) ∧
    -(if tiltedWeight p alpha l = 0 then 0 else
      tiltedWeight p alpha l * Real.log (tiltedWeight p alpha l)) ≤
        4*(tiltedWeight p alpha l * digitCost (prob p l)) := by
  have hZ := fullPowerSum_pos hk p ha
  have hw0 : 0 ≤ tiltedWeight p alpha l :=
    div_nonneg (Real.rpow_nonneg (prob_nonneg p l) alpha) hZ.le
  have hw1 : tiltedWeight p alpha l ≤ 1 := by
    apply (div_le_one hZ).mpr
    exact Finset.single_le_sum (fun a _ => Real.rpow_nonneg (prob_nonneg p a) alpha)
      (Finset.mem_univ l)
  by_cases hw : tiltedWeight p alpha l = 0
  · simp [hw]
  · have hwpos : 0 < tiltedWeight p alpha l := lt_of_le_of_ne hw0 (Ne.symm hw)
    have hp : 0 < prob p l := by
      apply lt_of_le_of_ne (prob_nonneg p l)
      intro hz
      exact hw (by simp [tiltedWeight, ← hz, Real.zero_rpow (by linarith [ha.1] : alpha ≠ 0)])
    have hlogw : Real.log (tiltedWeight p alpha l) =
        alpha * Real.log (prob p l) - Real.log (powerSum p alpha) := by
      rw [tiltedWeight, Real.log_div (Real.rpow_pos_of_pos hp alpha).ne' hZ.ne',
        Real.log_rpow hp alpha]
    have hid : -(tiltedWeight p alpha l * Real.log (tiltedWeight p alpha l)) =
        alpha * (tiltedWeight p alpha l * digitCost (prob p l)) +
          tiltedWeight p alpha l * Real.log (powerSum p alpha) := by
      rw [hlogw]
      simp only [digitCost, one_div, Real.log_inv]
      ring
    simp only [if_neg hw]
    constructor
    · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hw0 (Real.log_nonpos hwpos.le hw1))
    · rw [hid]
      have hlogZ := Real.log_nonpos hZ.le (fullPowerSum_le_one p ha)
      have hterm := mul_nonpos_of_nonneg_of_nonpos hw0 hlogZ
      have hmul := mul_le_mul_of_nonneg_right ha.2
        (mul_nonneg hw0 (digitCost_nonneg p l))
      linarith

theorem omittedEntropySum_bounds {k : ℕ} (hk : 2 ≤ k) (r p : Simplex k)
    {xi alpha : ℝ} (hxi : 0 < xi) (hsmall : xi < 1/8) (ha : alpha ∈ Icc (2 : ℝ) 4)
    (hbad : ∀ l, prob r l ≤ 2*xi → prob p l ≤ 3*xi) :
    0 ≤ omittedEntropySum r p xi alpha ∧
    omittedEntropySum r p xi alpha ≤ 48*(k : ℝ)^5*xi^2*Real.log (1/xi) := by
  have hterm (l : Fin k) := tiltedEntropy_term_bounds hk p ha l
  constructor
  · apply Finset.sum_nonneg
    intro l _
    by_cases hg : prob r l ≤ 2*xi
    · simpa only [if_pos hg] using (hterm l).1
    · simp only [if_neg hg, le_refl]
  · have hsum : omittedEntropySum r p xi alpha ≤
        4*(omittedCostSum r p xi alpha / powerSum p alpha) := by
      rw [omittedCostSum, Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro l _
      by_cases hg : prob r l ≤ 2*xi
      · have h := (hterm l).2
        simp only [omittedPower, if_pos hg]
        simpa only [tiltedWeight, div_mul_eq_mul_div] using h
      · simp only [omittedPower, if_neg hg, zero_mul, zero_div, mul_zero, le_refl]
    have hcost := omittedTiltedCost_small hk r p hxi hsmall ha hbad
    nlinarith

end RiffleLowerV2.Types
